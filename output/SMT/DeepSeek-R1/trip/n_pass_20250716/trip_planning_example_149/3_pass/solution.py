from z3 import *

# Create city enumeration
City = Datatype('City')
City.declare('London')
City.declare('Santorini')
City.declare('Istanbul')
City = City.create()

# Create Z3 variables for each day (0 to 9 for days 1 to 10)
days = [Const(f'day_{i}', City) for i in range(10)]

s = Solver()

# Total days in each city must be: London=3, Santorini=6, Istanbul=3
s.add(Sum([If(d == City.London, 1, 0) for d in days]) == 3)
s.add(Sum([If(d == City.Santorini, 1, 0) for d in days]) == 6)
s.add(Sum([If(d == City.Istanbul, 1, 0) for d in days]) == 3)

# Day 5 (index 4) and Day 10 (index 9) must be in Santorini
s.add(days[4] == City.Santorini)
s.add(days[9] == City.Santorini)

# Valid transitions between consecutive days
for i in range(9):
    current = days[i]
    next_day = days[i+1]
    s.add(Or(
        current == next_day,  # Stay in the same city
        And(current == City.London, next_day == City.Santorini),  # London -> Santorini
        And(current == City.London, next_day == City.Istanbul),   # London -> Istanbul
        And(current == City.Santorini, next_day == City.London),  # Santorini -> London
        And(current == City.Istanbul, next_day == City.London)    # Istanbul -> London
    ))

# Find and print a valid itinerary
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
    print("Valid 10-day itinerary found:")
    for day, city in enumerate(itinerary, start=1):
        print(f"Day {day}: {city}")
else:
    print("No valid itinerary exists for the given constraints.")