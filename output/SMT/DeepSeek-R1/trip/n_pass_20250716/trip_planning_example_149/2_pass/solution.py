from z3 import *

# Create city enumeration
City = Datatype('City')
City.declare('London')
City.declare('Santorini')
City.declare('Istanbul')
City = City.create()

# Create Z3 variables for each day
days = [Const('day_%d' % i, City) for i in range(10)]

s = Solver()

# Constraints for total days in each city
london_days = Sum([If(d == City.London, 1, 0) for d in days])
santorini_days = Sum([If(d == City.Santorini, 1, 0) for d in days])
istanbul_days = Sum([If(d == City.Istanbul, 1, 0) for d in days])

s.add(london_days == 3)
s.add(santorini_days == 6)
s.add(istanbul_days == 3)

# Day 5 (index 4) and Day 10 (index 9) must be in Santorini
s.add(days[4] == City.Santorini)
s.add(days[9] == City.Santorini)

# Valid transitions between consecutive days
for i in range(9):
    current = days[i]
    next_day = days[i+1]
    s.add(Or(
        current == next_day,
        And(current == City.London, next_day == City.Santorini),
        And(current == City.London, next_day == City.Istanbul),
        And(current == City.Santorini, next_day == City.London),
        And(current == City.Istanbul, next_day == City.London)
    ))

# Check for a solution and print the itinerary
if s.check() == sat:
    m = s.model()
    itinerary = []
    for i in range(10):
        d_val = m.eval(days[i])
        if d_val == City.London:
            itinerary.append("London")
        elif d_val == City.Santorini:
            itinerary.append("Santorini")
        else:
            itinerary.append("Istanbul")
    print("Day 1 to Day 10 Itinerary:")
    for day, city in enumerate(itinerary, start=1):
        print(f"Day {day}: {city}")
else:
    print("No valid itinerary found.")