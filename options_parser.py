# coding: utf-8
# options_parser, a state monad approach, refactor-ed from ysid

"""
A very general/limited options parser. We view option as three parts,
match, take and document. The match is a function from state(combined
by the position, index and offset in argv, and argv) to tuple of
priority and new state. Every match should not change the program
state, and we'll call the match of every option. But we only call the
take part of the one with greatest priority. The take is a (not pure)
function from (match-result, state) to (take-result, state). When
take-result is not None, it should be true, otherwise indicating
failure. Document has two parts, prefix and description.

Construction of match from string is provided for convenience. For
example, 'file|in-file' is a match with option '--file' or
'--in-file'. And this match also accept prefix match with lower
priority.

Take can be a type, which acted as a converter, and the dest is last
part of match string.

Example:

import options_parser
parser = options_parser.Parser(None, "description")
parser.add_help()
value = 20
parser.add_option("value", int, "INT::integer value")
# '--value 10' will set value to 10

parser.add_option(
  "VALUE",
  value().apply(lambda x: int(x) * 10).bind(Flag(dest="value")),
  "INT::set value to 10 times")
# '--VALUE 10' will set value to 100

L = locals()
def local_set(n, v):
  L[n] = v
parser.add_option(
  value().apply(lambda v: re.match("^[0-9]+$", v) and MATCH_POSITION),
  Take(lambda mr, state: (local_set("value", int(mr.match_arg())), state)),
  Document("INT", "set int value"))
# '1234' will set value to 1234, where options_parser.value is a state
# monad(a function from state to (x, state), x is any type).

parser.add_option(
  value().apply(lambda v: re.match("^-+value-[0-9]+$", v) and MATCH_UNIQUE),
  Take(lambda mr, state: (local_set("value", int(mr.match_arg()[6:])), state)),
  Document("--value-[0-9]+", "set int value"))
# '--value-5678' will set value to 5678
"""

import sys
import inspect

class Position(object):
  def __init__(self, index, off):
    self.index = index
    self.off = off

  def __repr__(self):
    return "(%s, %s)" % (self.index, self.off)

  def __cmp__(self, o):
    return cmp((self.index, self.off), (o.index, o.off))

def safe_get(a, i, dft=None):
  if i < len(a): return a[i]
  return dft

def get_arg(pos, argv):
  "return arg, new-pos"
  np = Position(pos.index, pos.off)
  if np.index >= len(argv):
    return None, np
  if np.index < len(argv):
    off = np.off
    np.off = 0
    np.index += 1
    return argv[np.index - 1][off:], np
  return None, np

def get_match_arg(pos, argv):
  "return arg, new-pos for a match arg. ignore '-' at start and stop at '=''"
  np = Position(pos.index, pos.off)
  off = np.off
  index = np.index
  if index >= len(argv):
    return None, np
  if index < len(argv):
    if off == 0:
      while safe_get(argv[index], off) == '-':
        off += 1
    stop = off
    while safe_get(argv[index], stop) not in (None, '='):
      stop += 1
    np.off = stop + 1
    if np.off >= len(argv[index]):
      np.off = 0
      np.index += 1
    return argv[index][off:stop], np
  return None, np

MATCH_NO = 0
MATCH_POSITION = 10
MATCH_PREFIX = 1000
MATCH_UNIQUE = 10000

class State(object):
  def __init__(self, pos, argv):
    self.pos = pos
    self.argv = argv

  def __repr__(self):
    s = []
    for i, a in enumerate(self.argv):
      if i == self.pos.index:
        o = self.pos.off
        s.append(a[:o] + "|" + a[o:])
      else:
        s.append(a)
    return "[" + (", ".join(s)) + "]"

# this is *not* a general monad implementation
class Monad(object):
  "Common methods of Monad, based on bind and wrap"
  def apply(self, func):
    def f(v):
      return self.wrap(func(v))
    return self.bind(f)

  def vapply(self, func):
    return self.apply(lambda v: func(*v))

  def many(self):
    def f(v_vs):
      v, vs = v_vs
      if v is None:
        return self.wrap(vs)
      vs.append(v)
      return self.apply(lambda x: (x, vs)).bind(f)
    return self.apply(lambda x: (x, [])).bind(f)

  def times(self, n):
    def f(v_vs):
      v, vs = v_vs
      if v is not None: vs.append(v)
      if v is None or len(vs) >= n:
        return self.wrap(vs)
      return self.apply(lambda x: (x, vs)).bind(f)
    if not n: return self.wrap([])
    return self.apply(lambda x: (x, [])).bind(f)

def gather(*monads):
  assert len(monads) >= 1
  if len(monads) == 1:
    return monads[0].apply(lambda v: (v,))
  def f1(x1):
    return gather(*(monads[1:])).apply(lambda vs: (x1,) + vs)
  return monads[0].bind(f1)

class StateMonad(Monad):
  def __init__(self, func):
    if isinstance(func, StateMonad):
      self.func = func.func
    else:
      self.func = func

  def __call__(self, s):
    return self.func(s)

  @classmethod
  def wrap(cls, x):
    def f(s):
      return x, s
    return StateMonad(f)

  def bind(self, f):
    def g(s):
      mv, ms = self.func(s)
      return f(mv)(ms)
    return StateMonad(g)

  @classmethod
  def put(s):
    def f(_):
      return None, s
    return StateMonad(f)

  @classmethod
  def get():
    def f(s):
      return s, s
    return StateMonad(f)

def value(convert=str, noopt=False, pre_check=None, post_check=None):
  def func(state):
    pos, argv = state.pos, state.argv
    v, np = get_arg(pos, argv)
    if noopt and pos.off == 0 and v and v[0] == '-':
      return None, State(pos, argv)
    if pre_check and not pre_check(v):
      return None, State(pos, argv)
    try:
      if v is not None: v = convert(v)
    except:
      return v, State(pos, argv)
    if v is None:
      return v, State(pos, argv)
    if post_check and not post_check(v):
      return None, State(pos, argv)
    return v, State(np, argv)
  return StateMonad(func)

def container(convert=str, pre_check=None, post_check=None):
  return value(convert=convert,
               noopt=True,
               pre_check=pre_check,
               post_check=post_check).many()

def sep_container(convert=str, pre_check=None, post_check=None):
  def func(sep):
    if not pre_check:
      pcheck = lambda s: s != sep
    else:
      pcheck = lambda s: (s != sep) and pre_check(s)
    def f(state):
       vs, state = value(convert=convert,
             pre_check=pcheck,
             post_check=post_check).many()(state)
       sepv, state = value()(state)
       if sepv != sep:
         raise RuntimeError("expect separator '%s'(got '%s')" % (sep, sepv))
       return vs, state
    return StateMonad(f)
  return func

class Take(object):
  def __init__(self, func):
    self.func = func
    if isinstance(func, Take):
      self.func = func.func

  def __call__(self, match_result, state):
    return self.func(match_result, state)

  @classmethod
  def from_func(cls, func, nargs=None):
    if nargs is None:
      p = inspect.getargspec(func)
      if p[1] or p[2]:
        raise RuntimeError("varargs and keywords not supported")
      nargs = len(p[0])
    return value().times(nargs).vapply(func)

class MatchResult(object):
  def __init__(self, priority, state):
    self.priority = priority
    self.state = state

  def __cmp__(self, o):
    return cmp(self.priority, o.priority)

  def match_arg(self):
    return get_match_arg(self.state.pos, self.state.argv)[0]

class Item(object):
  def __init__(self, match, take, doc, grp):
    self.match = match
    self.take = take
    self.doc = doc
    self.group = grp
    self.active = True

class Document(object):
  def __init__(self, prefix, desc):
    self.prefix = prefix
    self.desc = desc

def str_match(s):
  ms = s.split("|")
  def func(state):
    old_state = State(state.pos, state.argv)
    pos, argv = state.pos, state.argv
    assert pos.index < len(argv)
    if pos.off == 0 and safe_get(argv[pos.index], 0) != '-':
      return MatchResult(MATCH_NO, old_state), state
    arg, mpos = get_match_arg(pos, argv)
    if arg is None:
      return MatchResult(MATCH_NO, old_state), State(mpos, argv)
    for m in ms:
      if arg == m:
        return MatchResult(MATCH_UNIQUE, old_state), State(mpos, argv)
    for m in ms:
      if m.startswith(arg):
        return MatchResult(MATCH_PREFIX, old_state), State(mpos, argv)
    return MatchResult(MATCH_NO, old_state), State(mpos, argv)
  return func

def _getscope(index):
  L = None
  stack = inspect.stack()
  try:
    L = stack[index][0].f_locals
  finally:
    del stack
  return L

class Flag(StateMonad):
  def __init__(self, dest=None, scope=None):
    self.dest = dest
    self.scope = scope
    if scope is None:
      self.scope = _getscope(2)

  def func(self, v):
    self.scope[self.dest] = v
    return StateMonad.wrap(None)

class Parser(object):

  def __init__(self, parent, desc):
    self.parent = parent
    self.desc = desc
    self.current_group = ""
    self.items = []
    self.disable_groups = {}

  def at_group(g):
    self.current_group = g

  def disable_group(g):
    self.disable_groups.add(g)

  def enable_group(g):
    self.disable_groups.erase(g)

  def add_option(self, match, take, doc=""):
    """This function adds a option item to the parser.

    'match' can be any function from state to (priority/MatchResult,
    state).

    'match' can be a string, and in this case, we split 'match' by
    '|', and try to match current argument to every parts.

    'take' can be a Flag(store to to given scope, the default scope is
    the caller's locals). If 'take' is a string, we'll build a Flag
    with dest equal to 'take'. If take is a Flag(built or given), and
    the dest is not set, we'll try to get the dest from 'match' if
    it's a string. You're refered to class Flag for details.

    'take' can be a StateMonad, in this case, the Really Take is build
    with MatchResult ignored.

    'take' can be a general Python function, we'll build a real Take
    who consumes the same number arguments from state as that
    function(str only, since in Python, i think, we can't get the
    parameters type).

    'doc' can be an instance of Document. And 'doc' can be a string,
    just the description. And if 'match' is a string, we'll aslo set
    the prefix part as concatenation of '--' and 'match'.
    """
    match_o = match
    if isinstance(match, str):
      match = str_match(match)
    if isinstance(doc, str) and isinstance(match_o, str):
      doc = Document("--" + match_o, desc)
    elif isinstance(doc, str):
      doc = Document("", desc)
    locals_ = _getscope(2)
    if isinstance(match_o, str):
      match_dest = match_o.split("|")[-1].replace("-", "_")
    if isinstance(take, type):
      if not match_dest:
        raise RuntimeError("can't get dest")
      take = value(convert=take).bind(Flag(dest=match_dest, scope=locals_))
    if isinstance(take, Flag):
      if take.dest is None:
        if not match_dest:
          raise RuntimeError("can't get dest")
        take.dest = match_dest
      take = value().bind(take)
    if isinstance(take, StateMonad):
      t = take
      take = Take(lambda mr, s: t(s))
    if take is not None and not isinstance(take, Take):
      take_inspect = inspect.getargspec(take)
      if len(take_inspect[0]) == 1 and not take_inspect[1] and not take_inspect[2]:
        t = take
        take = Take(lambda mr, s: t(s))
      elif len(take_inspect[0]) == 2 and not take_inspect[1] and not take_inspect[2]:
        take = Take(take)
      else:
        raise RuntimeError("unsupported take %s(of type %s)" % (take, type(take)))
    item = Item(match, take, doc, self.current_group)
    self.items.append(item)
    return item

  def match_results(self, state):
    r = []
    for i in self.items:
      if i.group in self.disable_groups: continue
      if not i.active: continue
      mr, ms = i.match(state)
      if not isinstance(mr, MatchResult):
        mr = MatchResult(mr, state)
      r.append((mr, ms, i))
    if self.parent:
      r = r + self.parent.match_results(state)
    return r

  def parse(self, argv=None, pos=None):
    "return status, position"
    if argv is None: argv = sys.argv[1:]
    if isinstance(argv, State):
      state = argv
    else:
      if not pos: pos = Position(0, 0)
      state = State(pos, argv)
    state = State(state.pos, state.argv)
    while state.pos.index < len(state.argv):
      match_results = self.match_results(state)
      match_results = [i for i in match_results if i[0].priority > 0]
      match_results.sort(cmp=lambda x, y: cmp(y[0], x[0]))
      if not match_results:
        return "unmatch", state
      if len(match_results) >= 2 and match_results[0][0] == match_results[1][0]:
        return "multi-match", state
      match_result, match_state, item = match_results[0]
      take_result, take_state = item.take(match_result, match_state)
      if take_result is None:
        pass
      elif not take_result:
        return "failed", state
      state = take_state
    return True, state

  def add_help(self, match=None):
    if not match: match = "h|help"
    def help_func(mr, state):
      print >>sys.stderr, self.help_message()
      quit()
    self.add_option(match, help_func, "print help message")

  def help_message(self, line_width=80):
    hm = ""
    if len(self.desc): hm = self.desc + "\n\n"
    desc_off = 20
    def next_pos(s, off):
      n = s.find("\n", off)
      if n == -1: n = len(s)
      space = off
      while space < len(s):
        if s[space].isspace(): break
        space += 1
      return space
    def split_desc(desc, width):
      lines = []
      while len(desc) >= width:
        i = 0
        while i < len(desc):
          n = next_pos(desc, i + 1)
          if n > width or n >= len(desc):
            if i == 0: i = n
            break
          i = n
          if desc[n] == "\n": break
        lines.append(desc[:i])
        desc = desc[i + 1:]
      if desc: lines.append(desc)
      return lines
    for i in self.items:
      line = i.doc.prefix
      desc = i.doc.desc
      if len(line) >= desc_off and desc:
        hm += line + "\n"
        line = ""
      if desc:
        line += " " * (desc_off - len(line))
        lines = split_desc(desc, line_width - desc_off)
        for l in lines:
          if line:
            line += l
            hm += line + "\n"
            line = ""
          else:
            hm += (" " * desc_off) + l + "\n"
      if line:
        hm += line + "\n"
    return hm

PARSER = None

def check_init():
  global PARSER
  if not PARSER:
    PARSER = Parser(None, "default options parser")

def add_option(match, take, doc):
  check_init()
  return PARSER.add_option(match, take, doc)

def add_help(match=None):
  check_init()
  return PARSER.add_help(match)

def parse(argv=None, pos=None):
  check_init()
  return PARSER.parse(argv, pos)

if __name__ == "__main__":
  a = 10
  a_str = "a-str"
  vs = []
  num = 13
  f = False
  class Int(object):
    def __init__(self, *args):
      print "Int args", args
      self.value = int(*args)
    def __repr__(self):
      return "Int(%s)" % self.value
  def print_ab(a, b):
    print "a = %s b = %s" % (a, b)
  L = locals()
  def local_set(dest, v):
    L[dest] = v
  parser = Parser(None, "naive")
  parser.add_help()
  parser.add_option("a", int, "INT::integer")
  parser.add_option("a-str", str, "STR::str and very long description of help message.")
  parser.add_option("num", int, "INT::number")
  parser.add_option("vs",
                    container(str).apply(lambda xs: vs.extend(xs)),
                    "STR+::every item is append to vs")
  parser.add_option("sep-vs",
                    value().bind(sep_container(str)).apply(lambda xs: vs.extend(xs)),
                    "SEP STR+ SEP::every item is append to vs")
  parser.add_option("func-ab",
                    gather(value(), value()).vapply(print_ab),
                    "A B::print a and b")
  parser.add_option("set-f",
                    value(convert=lambda x:bool(int(x))).bind(Flag(dest="f")),
                    "BOOL::set f")
  parser.add_option("f-true",
                    Take(lambda mr, state: (local_set("f", True), state)),
                    "set f to true")
  parser.add_option("f-false",
                    Take(lambda mr, state: (local_set("f", False), state)),
                    "set f to false")
  parser.add_option(
      "f|no-f",
      Take(lambda mr, state: (local_set("f", mr.match_arg().startswith("f")), state)),
      "f or not")
  import re
  parser.add_option(
      value().apply(lambda v: re.match("^[0-9]+$", v) and MATCH_POSITION),
      Take(lambda mr, state: (local_set("a", int(mr.match_arg())), state)),
      Document("INT", "", "set int value"))
  parser.add_option(
      value().apply(lambda v: re.match("^-+value-[0-9]+$", v) and MATCH_UNIQUE),
      Take(lambda mr, state: (local_set("a", int(mr.match_arg()[6:])), state)),
      Document("--value-[0-9]+", "", "set int value"))
  def clear(L):
    while L: L.remove(L[0])
  parser.add_option(
      "clear-vs",
      Take.from_func(lambda: clear(vs)),
      "clear vs")
  parser.add_option(
      lambda state: (MatchResult(0, state), state),
      None,
      Document("", "", "only for help message"))
  r, state = parser.parse()
  print r, state
  print a, type(a)
  print num, type(num)
  print a_str, type(a_str)
  print vs, type(vs)
  print f, type(f)
