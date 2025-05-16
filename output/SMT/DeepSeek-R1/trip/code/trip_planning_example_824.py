from z3 import *

# Define flight days between cities
flight1 = Int('flight1')  # Berlin to Split
flight2 = Int('flight2')  # Split to Lyon
flight3 = Int('flight3')  # Lyon to Lisbon
flight4 = Int('flight4')  # Lisbon to Bucharest
flight5 = Int('flight5')  # Bucharest to Riga
flight6 = Int('flight6')  # Riga to Tallinn

s = Solver()

# Flight days must match fixed intervals and city connections
s.add(flight1 == 5)  # Leave Berlin on day5
s.add(flight2 == 7)  # Leave Split on day7
s.add(flight3 == 11) # Leave Lyon on day11
s.add(flight4 == 13) # Leave Lisbon on day13
s.add(flight5 == 15) # Leave Bucharest on day15
s.add(flight6 == 19) # Leave Riga on day19

# Validate days in each city
s.add(flight2 - flight1 == 2)  # Split: 5-7 (3 days)
s.add(flight3 - flight2 == 4)  # Lyon: 7-11 (5 days)
s.add(flight4 - flight3 == 2)  # Lisbon: 11-13 (3 days)
s.add(flight5 - flight4 == 2)  # Bucharest: 13-15 (3 days)
s.add(flight6 - flight5 == 4)  # Riga: 15-19 (5 days)
s.add(22 - flight6 + 1 == 4)   # Tallinn: 19-22 (4 days)

if s.check() == sat:
    schedule = []
    for day in range(1, 23):
        cities = []
        # Berlin (1-5)
        if day <= 5:
            cities.append("Berlin")
        # Split (5-7)
        if day >= 5 and day <= 7:
            if day == 5:
                cities.append("Berlin")
            cities.append("Split")
        # Lyon (7-11)
        if day >= 7 and day <= 11:
            if day == 7:
                cities.append("Split")
            cities.append("Lyon")
        # Lisbon (11-13)
        if day >= 11 and day <= 13:
            if day == 11:
                cities.append("Lyon")
            cities.append("Lisbon")
        # Bucharest (13-15)
        if day >= 13 and day <= 15:
            if day == 13:
                cities.append("Lisbon")
            cities.append("Bucharest")
        # Riga (15-19)
        if day >= 15 and day <= 19:
            if day == 15:
                cities.append("Bucharest")
            cities.append("Riga")
        # Tallinn (19-22)
        if day >= 19:
            if day == 19:
                cities.append("Riga")
            cities.append("Tallinn")
        schedule.append(cities)
    # Print the schedule
    for idx, cities in enumerate(schedule):
        print(f"Day {idx + 1}: {', '.join(cities)}")
else:
    print("No solution found")