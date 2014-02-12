# coding: utf-8
# options_parser, a state monad approach, refactor-ed from ysid

"""A very general/limited options parser. We view option as three parts, match,
take and document. The match is a function from state(combined by the position,
index and offset in argv, and argv) to tuple of priority and new state. Every
match should not change the program state, and we'll call the match of every
option. But we only call the take part of the one with greatest priority. The
take is a (not pure) function from match-result to take-result. When error of
take-result is not None, it's indicating failure message. Document has two
parts, prefix and description.

Construction of match from string is provided for convenience. For example, '-f
<file> --in-file FILE', or '-f, --in-file FILE' is a match with option '-f' or
'--in-file'. And this match also accept prefix with lower priority.

Take can be a type, which acted as a converter, and the dest is last part of the
match options.

Example:

import options_parser
parser = options_parser.Parser("description")
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
  Take(lambda mr: TakeResult(_=local_set("value", int(mr.match_arg())), state=mr.state)),
  Document("INT", "set int value"))
# '1234' will set value to 1234, where options_parser.value is a state
# monad(a function from state to (x, state), x is any type).

parser.add_option(
  value().apply(lambda v: re.match("^-+value-[0-9]+$", v) and MATCH_EXACT),
  Take(lambda mr: TakeResult(_=local_set("value", int(mr.match_arg()[6:])), state=mr.state)),
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

class Circumstance(object):
  pass

class State(object):
  def __init__(self, pos, argv, circumstance=None):
    self.pos = pos
    self.argv = argv
    self.circumstance = circumstance or Circumstance()

  def __repr__(self):
    s = []
    for i, a in enumerate(self.argv):
      if i == self.pos.index:
        o = self.pos.off
        s.append(a[:o] + "|" + a[o:])
      else:
        s.append(a)
    return "[" + (", ".join(s)) + "]"

MATCH_NO = 0
MATCH_POSITION = 10
MATCH_PREFIX = 1000
MATCH_EXACT = 10000

class MatchResult(object):
  def __init__(self, **kwds):
    self.priority = kwds.get("priority", None)
    self.state = kwds.get("state", None)
    self.start = kwds.get("start", None)

  def match_arg(self):
    return get_match_arg(self.start.pos, self.start.argv)

class TakeResult(object):
  def __init__(self, **kwds):
    self.state = kwds.get("state", None)
    self.error = kwds.get("error", None)

class MatchFromDescription(object):
  def desc_split(self, s):
    ret = []
    s = s.strip()
    while s:
      c = s[0]
      if c.isspace():
        s = s.strip()
        continue
      if c == ',':
        s = s[1:]
        continue
      if c == '[':
        ret.append(c)
        s = s[1:].lstrip(" =")
        continue
      if c == ']':
        ret.append(c)
        s = s[1:]
        continue
      if c == '-':
        if len(s) > 1 and s[1] != '-':
          ret.append(s[:2])
          s = s[2:].lstrip(" =")
          continue
        w = ""
        for c in s:
          if c in " [=": break
          w += c
        ret.append(w)
        s = s[len(w):].lstrip("[")
        continue
      if s == '<':
        w, s = s.split('>', 1)
        ret.append(w)
        s = s.strip()
        continue
      w, s = (s.split(" ", 1) + [""])[:2]
      ret.append(w)
    return ret

  def __init__(self, doc):
    self.num_args = 0;
    self.is_arg_optional = 0
    self.is_raw = 0
    self.doc = doc
    self.name = ""
    self.opts = []
    doc = doc.strip()
    if not doc.startswith("-"):
      self.init_not_doc()
      return
    vs = self.desc_split(doc)
    self.is_arg_optional = "[" in vs
    vs = [i for i in vs if i != "[" and i != "]"]
    for v in vs:
      if v.startswith("-"):
        self.opts.append(v.lstrip("-"))
        na = 0
        continue
      na += 1
      if na > self.num_args: self.num_args = na
    if self.opts:
      self.name = self.opts[-1]

  def __repr__(self):
    return "MatchFromDescription(name=%s, opts=%s, doc=%s, is_raw=%s, num_args=%s, is_arg_optional=%s)" % (
        self.name, self.opts, self.doc, self.is_raw, self.num_args, self.is_arg_optional)

  def init_not_doc(self):
    if self.doc.startswith("|"):
      self.is_raw = true;
      self.opts = split(doc.substr(1), "|");
      if self.opts: self.name = self.opts[-1]
      self.doc = ", ".join(self.opts)
      return
    self.opts = self.doc.split("|");
    if self.opts: self.name = self.opts[-1]
    self.doc = ""
    for o in self.opts:
      if self.doc: self.doc += ", ";
      self.doc += (len(o) == 1 and "-" or "--") + o;

  def match(self, s):
    mr = MatchResult()
    mr.priority = 0
    arg, np = get_match_arg(s.pos, s.argv)
    mr.start = s;
    mr.state = State(np, s.argv, s.circumstance)
    if not arg: return mr
    first_arg, _ = get_arg(Position(s.pos.index, 0), s.argv)
    if self.is_raw or (s.pos.off == 0 and first_arg.startswith("--")):
      for o in self.opts:
        if o == arg:
          mr.priority = MATCH_EXACT
          return mr
    if arg and s.pos.off == 0 and not self.is_raw and first_arg.startswith("--"):
      for o in self.opts:
        if len(arg) < len(o) and o[:len(arg)] == arg:
          mr.priority = MATCH_PREFIX
          return mr
    if self.is_raw: return mr
    if arg and not first_arg.startswith("--"):
      for o in self.opts:
        if len(o) != 1: continue
        if arg[0] != o: continue
        mr.priority = MATCH_EXACT
        off = s.pos.off
        if off == 0 and off < len(first_arg) and first_arg[off] == '-': off += 1
        off += 1
        if off < len(first_arg):
          mr.state.pos.index = s.pos;
          mr.state.pos.off = off;
          if first_arg[off] == '=':
            mr.state.pos.off += 1
        return mr
    return mr

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

# this is *not* a general monad implementation
class Monad(object):
  "Common methods of Monad, based on bind and wrap"
  def apply(self, func):
    def f(v):
      return self.wrap(func(v))
    return self.bind(f)

  def vapply(self, func):
    return self.apply(lambda v: func(*v))

  def list_apply(self, func):
    return self.apply(lambda v: [func(i) for i in v])

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
    return v, State(np, argv, state.circumstance)
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

  def __call__(self, match_result):
    return self.func(match_result)

  @classmethod
  def from_func(cls, func, nargs=None):
    if nargs is None:
      p = inspect.getargspec(func)
      if p[1] or p[2]:
        raise RuntimeError("varargs and keywords not supported")
      nargs = len(p[0])
    return cls.from_value(value().times(nargs).vapply(func))

  @classmethod
  def from_value(cls, v):
    def func(mr):
      _, s = v(mr.state)
      tr = TakeResult()
      tr.state = s
      return tr
    return Take(func)

class Match(object):
  def __init__(self, func):
    self.func = func
    if isinstance(func, Match):
      self.func = func.func

  def __call__(self, state):
    ret = self.func(state)
    if isinstance(ret, MatchResult): return ret
    if isinstance(ret, tuple):
      p, s = ret
      return MatchResult(state=s, priority=p, start=state)
    raise RuntimeError("invalid match ...")

class Item(object):
  def __init__(self, match, take, doc):
    self.match = match
    self.take = take
    self.doc = doc
    self.active = True

class Document(object):
  def __init__(self, prefix, desc):
    self.prefix = prefix
    self.desc = desc

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

  def __init__(self, desc):
    self.desc = desc
    self.items = []
    self.parsers = {}
    self.add_parser(self, 0)
    self.active = True

  def toggle(self):
    self.active = not self.active

  def add_parser(self, parser, priority=0):
    if not priority in self.parsers:
      self.parsers[priority] = []
    self.parsers[priority].append(parser)

  def add_option(self, match, take, doc="", prefix=None, scope_add=0):
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
    the prefix as match
    """
    match_o = match
    mfd = None
    if isinstance(match, str):
      mfd = MatchFromDescription(match)
      match = mfd.match
    if isinstance(doc, str) and mfd and prefix is None:
      prefix = mfd.doc
    if isinstance(doc, str):
      doc = Document(prefix or "", doc)
    locals_ = _getscope(2 + scope_add)
    if mfd:
      match_dest = mfd.name.replace("-", "_")
    if isinstance(take, type):
      if not match_dest:
        raise RuntimeError("can't get dest")
      take = Take.from_value(value(convert=take).bind(Flag(dest=match_dest, scope=locals_)))
    if isinstance(take, Flag):
      if take.dest is None:
        if not match_dest:
          raise RuntimeError("can't get dest")
        take.dest = match_dest
      take = Take.from_value(value().bind(take))
    if isinstance(take, StateMonad):
      take = Take.from_value(take)
    if take is not None and not isinstance(take, Take):
      take_inspect = inspect.getargspec(take)
      if len(take_inspect[0]) == 1 and not take_inspect[1] and not take_inspect[2]:
        take = Take(take)
      else:
        raise RuntimeError("unsupported take %s(of type %s)" % (take, type(take)))
    if not isinstance(match, Match):
      match = Match(match)
    item = Item(match, take, doc)
    self.items.append(item)
    return item

  def match_results(self, state):
    results = []
    if not self.active: return results
    for p, parsers in self.parsers.iteritems():
      for parser in parsers:
        l = []
        if parser != self:
          l = parser.match_results(state)
        else:
          for i in self.items:
            if not i.active: continue
            mr = i.match(state)
            assert isinstance(mr, MatchResult)
            if mr.priority <= 0: continue
            l.append((mr, i))
        results += l
    return results

  def parse(self, argv=None, pos=None, circumstance=None):
    "return status, position"
    if argv is None: argv = sys.argv[1:]
    if isinstance(argv, State):
      state = argv
    else:
      if not pos: pos = Position(0, 0)
      state = State(pos, argv, circumstance)
    state = State(state.pos, state.argv, state.circumstance)
    while state.pos.index < len(state.argv):
      match_results = self.match_results(state)
      mp = max(max(mr.priority for mr, item in match_results), 1) if match_results else 1
      match_results = [(mr, item) for mr, item in match_results if mr.priority == mp]
      if not match_results:
        return "unmatch", state
      if len(match_results) >= 2:
        return "multi-match", state
      match_result, item = match_results[0]
      take_result = item.take(match_result)
      if take_result.error is not None:
        return "take-error: %s" % take_result.error, take_result.state
      state = take_result.state
    return True, state

  def add_help(self, match=None):
    if not match: match = "-h, --help"
    def help_func(mr):
      print >>sys.stderr, self.help_message()
      quit()
    self.add_option(match, help_func, "print help message")

  def help_message(self, line_width=80, caller=None):
    if caller != self:
      hms = []
      for p, parsers in self.parsers.iteritems():
        for parser in parsers:
          hms.append((p, parser.help_message(line_width, self)))
      hms.sort(key=lambda x: x[0])
      return "\n".join([m for _, m in hms])
    hm = ""
    if len(self.desc): hm = self.desc + "\n\n"
    desc_off = 20
    def next_pos(s, off):
      space = off
      while space < len(s):
        if s[space].isspace(): break
        space += 1
      return space
    def split_line(s, width):
      lines = []
      while len(s) >= width:
        i = 0
        while i < len(s):
          n = next_pos(s, i + 1)
          if n > width or n >= len(s):
            if i == 0: i = n
            break
          i = n
        lines.append(s[:i])
        s = s[i + 1:]
      if len(s): lines.append(s)
      return lines
    def split_desc(desc, width):
      lines = []
      for line in desc.split("\n"):
        lines.extend(split_line(line, width))
      return lines
    for i in self.items:
      line = i.doc.prefix
      desc = i.doc.desc
      if not len(line) and not len(desc): continue
      if len(line) >= desc_off and desc:
        hm += line + "\n"
        line = ""
      if desc:
        if line: line += (" " * (desc_off - len(line)))
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
    PARSER = Parser("default options parser")

def add_option(match, take, doc):
  check_init()
  return PARSER.add_option(match, take, doc, scope_add=1)

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
  parser = Parser("naive options parser as every options splited as MATCH, TAKE, DOCUMENT.")
  parser.add_help()
  parser.add_option("-a INT", int, "integer")
  parser.add_option("--a-str STR", str, "str and very long description of help message.")
  parser.add_option("--num NUM", int, "number")
  parser.add_option("--vs <str>...",
                    container(str).apply(lambda xs: vs.extend(xs)),
                    "every item is append to vs")
  parser.add_option("--sep-vs <sep> <str>... <sep>",
                    value().bind(sep_container(str)).apply(lambda xs: vs.extend(xs)),
                    "every item is append to vs")

  parser.add_option("--func-ab A B",
                    gather(value(), value()).vapply(print_ab),
                    "print a and b")
  parser.add_option("--set-f",
                    value(convert=lambda x:bool(int(x))).bind(Flag(dest="f")),
                    "set f")
  parser.add_option("--f-true",
                    Take.from_func(lambda: local_set("f", True)),
                    "set f to true")
  parser.add_option("--f-false",
                    Take.from_func(lambda: local_set("f", False)),
                    "set f to false")
  import re
  parser.add_option(
      value().apply(lambda v: re.match("^[0-9]+$", v) and MATCH_POSITION),
      Take(lambda mr: TakeResult(_=local_set("a", int(mr.match_arg())), state=mr.state)),
      Document("INT", "set int value"))
  parser.add_option(
      value().apply(lambda v: re.match("^-+value-[0-9]+$", v) and MATCH_EXACT),
      Take(lambda mr: TakeResult(_=local_set("a", int(mr.match_arg()[6:])), state=mr.state)),
      Document("--value-[0-9]+", "set int value"))
  def clear(L):
    while L: L.remove(L[0])
  parser.add_option(
      "--clear-vs",
      Take.from_func(lambda: clear(vs)),
      "clear vs")
  parser.add_option(
      lambda state: MatchResult(priority=0, state=state),
      Take(None),
      Document("help message", "Not a option, just print a help message. This"
               " test very long help message. A very long message should be"
               " splited and formated to fixed width"))
  sub = Parser("sub")
  sub.toggle()
  def sub_print(a):
    print "sub arg", a
  sub.add_option("-a A", Take.from_func(sub_print), "arg print")
  sub.add_option("-b B", Take.from_func(sub_print), "arg print")
  parser.add_option(value().apply(lambda s: s == "sub" and MATCH_EXACT or MATCH_NO),
                    Take.from_func(lambda: sub.toggle()), "toggle active sub")
  sub.add_option(value().apply(lambda s: s == '--' and MATCH_EXACT or MATCH_NO),
                 Take.from_func(lambda: sub.toggle()),
                 "disable sub", prefix="--")
  parser.add_parser(sub, 1)
  r, state = parser.parse()
  print r, state
  print a, type(a)
  print num, type(num)
  print a_str, type(a_str)
  print vs, type(vs)
  print f, type(f)
