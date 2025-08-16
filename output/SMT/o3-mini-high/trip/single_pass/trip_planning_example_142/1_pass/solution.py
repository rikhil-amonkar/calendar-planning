from z3 import *
import json

# We'll represent the three cities as integers:
# 0: Madrid, 1: Dublin, 2: Tallinn
city_names = {0: "Madrid", 1: "Dublin", 2: "Tallinn"}

# We have 7 days (indexed 0...6 corresponding to Days 1..7).
# On each day we assign an integer variable "trip[i]" that indicates in which city you are.
# Note that if you fly on a day (i.e. the city changes from day i-1 to day i),
# then that day counts for both the previous city and the arrival city.

# Create 7 integer variables with domain {0,1,2}
trip = [Int(f"trip_{i}") for i in range(7)]

# For each day, restrict trip[i] to {0,1,2}
s = Solver()
for i in range(7):
    s.add(Or(trip[i] == 0, trip[i] == 1, trip[i] == 2))

# Introduce a Boolean flag for each day that indicates if a flight occurs that day.
# For day 0 there is no flight.
flight = [Bool(f"flight_{i}") for i in range(7)]
s.add(flight[0] == False)
for i in range(1, 7):
    # A flight occurs on day i if the city differs from the previous day.
    s.add(flight[i] == (trip[i] != trip[i-1]))

# We want exactly 2 flight days.
s.add(Sum([If(flight[i], 1, 0) for i in range(7)]) == 2)

# Allowed direct flights are only between Madrid and Dublin, or Dublin and Tallinn.
# Thus, when a flight (i.e. a change) occurs on day i (i>=1),
# then the transition (trip[i-1] -> trip[i]) must be one of:
#    Madrid -> Dublin, Dublin -> Madrid,
#    Dublin -> Tallinn, or Tallinn -> Dublin.
for i in range(1, 7):
    s.add(Implies(flight[i],
                  Or(And(trip[i-1] == 0, trip[i] == 1),  # Madrid -> Dublin 
                     And(trip[i-1] == 1, trip[i] == 0),  # Dublin -> Madrid
                     And(trip[i-1] == 1, trip[i] == 2),  # Dublin -> Tallinn
                     And(trip[i-1] == 2, trip[i] == 1)   # Tallinn -> Dublin
                  )))

# We must accumulate “days in city” counts as follows:
# • On Day 1 (index 0) we are only in the city trip[0].
# • For each day i>=1:
#    o If no flight is taken (trip[i] == trip[i-1]), then that day contributes 1 day in trip[i].
#    o If a flight IS taken (trip[i] != trip[i-1]), then day i is counted for both cities:
#         one day for the previous city (trip[i-1]) and one day for the arrival (trip[i]).
#
# Our trip requirements are:
#   • 4 days in Madrid (city 0)
#   • 3 days in Dublin (city 1)
#   • 2 days in Tallinn (city 2)
def city_count(city):
    cnt = If(trip[0] == city, 1, 0)
    for i in range(1, 7):
        # If no flight, add one day (if we are in that city on day i).
        # If a flight occurs on day i, add one day for the departure city AND one for the arrival.
        cnt = cnt + If(trip[i] == trip[i-1],
                       If(trip[i] == city, 1, 0),
                       (If(trip[i-1] == city, 1, 0) + If(trip[i] == city, 1, 0)))
    return cnt

s.add(city_count(0) == 4)  # Madrid: 4 days
s.add(city_count(1) == 3)  # Dublin: 3 days
s.add(city_count(2) == 2)  # Tallinn: 2 days

# There is a workshop in Tallinn that takes place between Day 6 and Day 7.
# This means on at least one of these days (Day 6 or Day 7) you must be present in Tallinn.
# Remember: On a flight day, you are in both the previous and current cities.
# For Day 6 (index 5):
#   If a flight takes place on Day 6 then the presence is {trip[4], trip[5]};
#   Otherwise it is only {trip[5]}.
# Similarly for Day 7 (index 6).
day6_present = If(flight[5],
                  Or(trip[4] == 2, trip[5] == 2),
                  trip[5] == 2)
day7_present = If(flight[6],
                  Or(trip[5] == 2, trip[6] == 2),
                  trip[6] == 2)

s.add(Or(day6_present, day7_present))

# Check for a solution.
if s.check() == sat:
    m = s.model()
    # Extract the trip plan as a list of integers.
    plan = [m.evaluate(trip[i]).as_long() for i in range(7)]
    
    # Build the itinerary day by day.
    # On Day 1 (index 0): presence = [trip[0]]
    # For day i>=1:
    #   If a flight occurs on that day then presence = [trip[i-1], trip[i]]
    #   Otherwise, presence = [trip[i]]
    itinerary = []
    for i in range(7):
        if i == 0:
            # Day 1: only one city.
            day_places = [city_names[plan[0]]]
        else:
            if plan[i] == plan[i-1]:
                day_places = [city_names[plan[i]]]
            else:
                day_places = [city_names[plan[i-1]], city_names[plan[i]]]
        # If only one city is present, output as a string.
        if len(day_places) == 1:
            itinerary.append({"day": i + 1, "place": day_places[0]})
        else:
            itinerary.append({"day": i + 1, "place": day_places})
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")