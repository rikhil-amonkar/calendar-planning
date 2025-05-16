from z3 import *

# Define the flight days
flight1_day = Int('flight1_day')  # Krakow to Paris
flight2_day = Int('flight2_day')  # Paris to Seville

s = Solver()

# Constraints
s.add(flight1_day >= 1, flight1_day <= 11)
s.add(flight2_day >= 1, flight2_day <= 11)
s.add(flight1_day == 5)  # Krakow must be 5 days (days 1-5)
s.add(flight2_day - flight1_day + 1 == 2)  # Paris must be 2 days
s.add(11 - flight2_day + 1 == 6)  # Seville must be 6 days
s.add(flight1_day < flight2_day)  # Order of flights

if s.check() == sat:
    m = s.model()
    f1 = m[flight1_day].as_long()
    f2 = m[flight2_day].as_long()
    schedule = []
    for day in range(1, 12):
        cities = []
        if day < f1:
            cities.append("Krakow")
        elif day == f1:
            cities.append("Krakow")
            cities.append("Paris")
        elif day < f2:
            cities.append("Paris")
        elif day == f2:
            cities.append("Paris")
            cities.append("Seville")
        else:
            cities.append("Seville")
        schedule.append(cities)
    # Print the schedule
    for idx, cities in enumerate(schedule):
        print(f"Day {idx + 1}: {', '.join(cities)}")
else:
    print("No solution found")