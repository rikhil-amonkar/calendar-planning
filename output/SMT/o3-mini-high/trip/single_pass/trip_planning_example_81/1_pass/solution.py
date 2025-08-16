from z3 import *
import json

# Create an enumeration for the three cities.
City, (Hamburg, Budapest, Mykonos) = EnumSort('City', ['Hamburg', 'Budapest', 'Mykonos'])

# We have 9 days. For each day i (1-indexed, but we use a 0-indexed list) we choose a city.
days = 9
x = [Const(f"x{i+1}", City) for i in range(days)]

s = Solver()

# Constraint: When flying (i.e. when the city changes from one day to the next)
# the flight must be direct. Allowed direct flights are:
#   Hamburg <-> Budapest and Budapest <-> Mykonos.
# (Note: There is no direct flight between Hamburg and Mykonos.)
for i in range(1, days):
    flight_day = (x[i] != x[i-1])
    # If flying then:
    #   if departing from Hamburg or Mykonos, you must fly to Budapest.
    #   if departing from Budapest, you must fly either to Hamburg or Mykonos.
    allowed = If(x[i-1] == Hamburg, x[i] == Budapest,
            If(x[i-1] == Mykonos, x[i] == Budapest,
            If(x[i-1] == Budapest, Or(x[i] == Hamburg, x[i] == Mykonos),
               True)))
    s.add(Implies(flight_day, allowed))

# Conference attendance constraints: On day 4 and day 9 you must be in Mykonos.
# Remember: if you fly on that day then you are in both the departure and arrival cities.
# So for day i (i>1) we require that Mykonos is one of the two cities.
# (For a non-flight day the only possibility is x[i]==Mykonos.)
s.add(Or(x[3] == Mykonos, x[2] == Mykonos))  # Day 4: index 3 (or from previous day index 2 if flight)
s.add(Or(x[8] == Mykonos, x[7] == Mykonos))  # Day 9: index 8 (or from previous day index 7 if flight)

# Exactly two flight days must occur. (Recall: flying on day i means x[i]!=x[i-1] for i>=1)
flight_days = [If(x[i] != x[i-1], 1, 0) for i in range(1, days)]
s.add(Sum(flight_days) == 2)

# The way we count days in each city:
#   For day1 the traveler is simply present in x[0].
#   For each later day i (i>=2), if there is no flight (x[i] == x[i-1])
#   then the traveler spends that day in the same single city.
#   If there is a flight (x[i] != x[i-1]) then day i “counts” for both the departing city and the arriving city.
#
# Thus, for each city, the total count is:
#    count(city) = I(x[0]==city)
#                  + for i=1 to 8: I(x[i]==city)  [the city you “arrive in” on day i]
#                  + for i=1 to 8: I(x[i] != x[i-1] and x[i-1]==city)  [the city you left on flight day]
#
# Required counts:
#   Mykonos: 6 days, Budapest: 3 days, Hamburg: 2 days.
def city_count(city):
    cnt = If(x[0] == city, 1, 0)
    for i in range(1, days):
        cnt = cnt + If(x[i] == city, 1, 0) \
                  + If(x[i] != x[i-1], If(x[i-1] == city, 1, 0), 0)
    return cnt

s.add(city_count(Hamburg) == 2)
s.add(city_count(Budapest) == 3)
s.add(city_count(Mykonos) == 6)

# Solve the constraints
if s.check() == sat:
    m = s.model()
    itinerary = []
    
    # Build an itinerary: For each day output a mapping "day": number, "place": ...
    # On a day with no flight, the traveler is in a single city.
    # On a flight day (x[i] != x[i-1]) the traveler is counted as being in both the previous and current city.
    for i in range(days):
        # For day 1 (index 0) no flight is possible.
        if i == 0:
            day_place = str(m.evaluate(x[i]))
        else:
            if m.evaluate(x[i]) != m.evaluate(x[i-1]):
                # Flight day: list both (previous day, current day)
                day_place = [str(m.evaluate(x[i-1])), str(m.evaluate(x[i]))]
            else:
                day_place = str(m.evaluate(x[i]))
        itinerary.append({"day": i+1, "place": day_place})
    
    # Prepare the JSON output
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")