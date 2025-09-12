# After evaluating the model for the cities
cities = [model.eval(c1), model.eval(c2), model.eval(c3), model.eval(c4), model.eval(c5)]
cities = [c.as_long() for c in cities]