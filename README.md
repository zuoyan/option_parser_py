# option_parser, a command line argv parsing module

## WHY another

Yes, it's another wheel, with some/little differences.

It follows the same design as
[the C++ library](http://github.com/zuoyan/options_parser), so i can avoid to be
confused by argparse, esp. with the reordering.

In options_parser, an option is just splited as (match, process,
document). Match is first called, the process correspending to the
highest match result is called and return the next position.

## Example

See

    python options_parser.py --help
