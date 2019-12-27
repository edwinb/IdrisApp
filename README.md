IdrisApp
========

Just a little experiment, in an attempt to find the simplest possible
IO-like type, extensible with states and exceptions, which supports linearity
when necessary, in order to encapsulate the most common things you might want
to combine in an application.

You can stick it at the bottom of your monad transformer stack if you like, or
use it to interpret your free monads or effect systems if you like.
Otherwise, define your interfaces and off you go!
