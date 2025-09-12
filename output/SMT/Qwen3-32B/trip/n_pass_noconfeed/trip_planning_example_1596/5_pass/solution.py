# Create a mapping from city names to durations using a Z3 function
city_to_duration = Function('city_to_duration', StringSort(), IntSort())
for city, dur in durations.items():
    s.add(city_to_duration(z3.StringVal(city)) == dur)