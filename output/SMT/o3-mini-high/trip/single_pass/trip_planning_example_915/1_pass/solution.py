from z3 import *
import json

# Map cities to integers:
# 0: Bucharest, 1: Venice, 2: Prague, 3: Frankfurt, 4: Zurich, 5: Florence, 6: Tallinn

def allowed_flight(a, b):
    # All flights are allowed in both directions except the special case
    # "from Zurich to Florence" which is only allowed in that direction (4 -> 5).
    return Or(
         And(a == 2, b == 6),  And(a == 6, b == 2),  # Prague <-> Tallinn
         And(a == 2, b == 4),  And(a == 4, b == 2),  # Prague <-> Zurich
         And(a == 5, b == 2),  And(a == 2, b == 5),  # Florence <-> Prague
         And(a == 3, b == 0),  And(a == 0, b == 3),  # Frankfurt <-> Bucharest
         And(a == 3, b == 1),  And(a == 1, b == 3),  # Frankfurt <-> Venice
         And(a == 2, b == 0),  And(a == 0, b == 2),  # Prague <-> Bucharest
         And(a == 0, b == 4),  And(a == 4, b == 0),  # Bucharest <-> Zurich
         And(a == 6, b == 3),  And(a == 3, b == 6),  # Tallinn <-> Frankfurt
         And(a == 3, b == 4),  And(a == 4, b == 3),  # Frankfurt <-> Zurich
         And(a == 4, b == 1),  And(a == 1, b == 4),  # Zurich <-> Venice
         And(a == 5, b == 3),  And(a == 3, b == 5),  # Florence <-> Frankfurt
         And(a == 2, b == 3),  And(a == 3, b == 2),  # Prague <-> Frankfurt
         And(a == 6, b == 4),  And(a == 4, b == 6),  # Tallinn <-> Zurich
         And(a == 4, b == 5)                     # Special: from Zurich to Florence
    )

# Create the solver.
solver = Solver()

# We have 26 days, numbered 0 to 25 (which correspond to days 1 to 26)
days = [Int(f"day_{i}") for i in range(26)]
for d in days:
    solver.add(And(d >= 0, d <= 6))  # each day is one of the 7 cities

# When a flight occurs (i.e. day[i] != day[i-1]) the flight must be allowed.
for i in range(1, 26):
    solver.add(Implies(days[i] != days[i-1], allowed_flight(days[i-1], days[i])))

# Count the number of flights: exactly 6 flights.
flight_count = Sum([If(days[i] != days[i-1], 1, 0) for i in range(1, 26)])
solver.add(flight_count == 6)

# City duration requirements (remember: on a day with a flight, the origin city gets credit too):
# count(city) = (number of days i with days[i]==city) + (for each i from 1 to 25, if days[i]!=days[i-1] and days[i-1]==city then +1)
required = {0: 3, 1: 5, 2: 4, 3: 5, 4: 5, 5: 5, 6: 5}
for city in range(7):
    count_expr = Sum([If(days[i] == city, 1, 0) for i in range(26)]) + \
                 Sum([If(And(days[i] != days[i-1], days[i-1] == city), 1, 0) for i in range(1, 26)])
    solver.add(count_expr == required[city])

# “Wedding in Venice” constraint: Some day between day 22 and day 26 (indices 21 to 25)
# In a flight day the day counts for both the flight origin and destination.
wedding_days = []
for i in range(21, 26):
    # Either you are in Venice on day i OR, if day i is a flight day, you were in Venice on the previous day.
    if i > 0:
        wedding_presence = Or(days[i] == 1, And(days[i-1] == 1, days[i] != 1))
    else:
        wedding_presence = (days[i] == 1)
    wedding_days.append(wedding_presence)
solver.add(Or(wedding_days))

# “Frankfurt Show” constraint: Some day between day 12 and day 16 (indices 11 to 15) you must be (or fly from) Frankfurt.
show_days = []
for i in range(11, 16):
    if i > 0:
        show_presence = Or(days[i] == 3, And(days[i-1] == 3, days[i] != 3))
    else:
        show_presence = (days[i] == 3)
    show_days.append(show_presence)
solver.add(Or(show_days))

# “Meeting friends in Tallinn” constraint: Some day between day 8 and day 12 (indices 7 to 11) you must be (or fly from) Tallinn.
tallinn_days = []
for i in range(7, 12):
    if i > 0:
        tallinn_presence = Or(days[i] == 6, And(days[i-1] == 6, days[i] != 6))
    else:
        tallinn_presence = (days[i] == 6)
    tallinn_days.append(tallinn_presence)
solver.add(Or(tallinn_days))

# Now solve the model. If a solution is found, output the 26–day itinerary as a JSON dictionary.
if solver.check() == sat:
    m = solver.model()
    mapping = {0: "Bucharest",
               1: "Venice",
               2: "Prague",
               3: "Frankfurt",
               4: "Zurich",
               5: "Florence",
               6: "Tallinn"}
    itinerary = []
    for i in range(26):
        day_city = m[days[i]].as_long()
        itinerary.append({"day": i + 1, "city": mapping[day_city]})
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found")