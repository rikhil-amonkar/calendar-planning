# Each city can only be visited once per day
[Or([Not(x[city_to_index(c, day)]) for c in cities if c!= city]) for city in cities for day in days]