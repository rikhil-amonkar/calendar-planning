from z3 import *

# Define flight days between cities
flight1 = Int('flight1')  # Paris to Vienna
flight2 = Int('flight2')  # Vienna to Riga
flight3 = Int('flight3')  # Riga to Barcelona
flight4 = Int('flight4')  # Barcelona to Krakow
flight5 = Int('flight5')  # Krakow to Hamburg
flight6 = Int('flight6')  # Hamburg to Edinburgh
flight7 = Int('flight7')  # Edinburgh to Stockholm

s = Solver()

# Constraints for fixed events
s.add(flight1 >= 2)  # Leave Paris on day 2 (after 2 days)
s.add(flight5 >= 10, flight5 <= 11)  # Hamburg days 10-11
s.add(flight6 == 12)  # Leave Hamburg on day 12 for Edinburgh
s.add(flight7 == 15)  # Leave Edinburgh on day 15 for Stockholm

# Duration constraints for each city
s.add(flight1 - 1 == 2 - 1)              # Paris: days 1-2 (2 days)
s.add(flight2 - flight1 + 1 == 4)        # Vienna: 4 days (flight1 to flight2)
s.add(flight3 - flight2 + 1 == 4)        # Riga: 4 days (flight2 to flight3)
s.add(flight4 - flight3 + 1 == 2)        # Barcelona: 2 days (flight3 to flight4)
s.add(flight5 - flight4 + 1 == 3)        # Krakow: 3 days (flight4 to flight5)
s.add(flight6 - flight5 + 1 == 2)        # Hamburg: 2 days (flight5 to flight6)
s.add(flight7 - flight6 + 1 == 4)        # Edinburgh: 4 days (flight6 to flight7)
s.add(27 - flight7 + 1 == 2)             # Stockholm: 2 days (flight7 to 27)

# Ensure flight order and direct flight connections
s.add(flight1 < flight2, flight2 < flight3, flight3 < flight4,
      flight4 < flight5, flight5 < flight6, flight6 < flight7)

# Direct flight checks
s.add(Or(flight1 == 2))  # Paris to Vienna is allowed
s.add(Or(flight2 == flight1 + 4 - 1))  # Vienna to Riga is allowed
s.add(Or(flight3 == flight2 + 4 - 1))  # Riga to Barcelona is allowed
s.add(Or(flight4 == flight3 + 2 - 1))  # Barcelona to Krakow is allowed
s.add(Or(flight5 == flight4 + 3 - 1))  # Krakow to Hamburg is allowed (if connected)
s.add(Or(flight6 == 12))  # Hamburg to Edinburgh is allowed
s.add(Or(flight7 == 15))  # Edinburgh to Stockholm is allowed

if s.check() == sat:
    m = s.model()
    schedule = []
    for day in range(1, 17):
        cities = []
        # Paris (1-2)
        if day <= 2:
            cities.append("Paris")
            if day == 2:
                cities.append("Vienna")
        # Vienna (2-5)
        if day > 2 and day <= m[flight2].as_long():
            if day == m[flight2].as_long():
                cities.append("Vienna")
                cities.append("Riga")
            else:
                cities.append("Vienna")
        # Riga (5-8)
        if day > m[flight2].as_long() and day <= m[flight3].as_long():
            if day == m[flight3].as_long():
                cities.append("Riga")
                cities.append("Barcelona")
            else:
                cities.append("Riga")
        # Barcelona (8-9)
        if day > m[flight3].as_long() and day <= m[flight4].as_long():
            if day == m[flight4].as_long():
                cities.append("Barcelona")
                cities.append("Krakow")
            else:
                cities.append("Barcelona")
        # Krakow (9-11)
        if day > m[flight4].as_long() and day <= m[flight5].as_long():
            if day == m[flight5].as_long():
                cities.append("Krakow")
                cities.append("Hamburg")
            else:
                cities.append("Krakow")
        # Hamburg (10-11)
        if day > m[flight5].as_long() and day <= m[flight6].as_long():
            if day == m[flight6].as_long():
                cities.append("Hamburg")
                cities.append("Edinburgh")
            else:
                cities.append("Hamburg")
        # Edinburgh (12-15)
        if day > m[flight6].as_long() and day <= m[flight7].as_long():
            if day == m[flight7].as_long():
                cities.append("Edinburgh")
                cities.append("Stockholm")
            else:
                cities.append("Edinburgh")
        # Stockholm (15-16)
        if day > m[flight7].as_long():
            cities.append("Stockholm")
        schedule.append(cities)
    for idx, cities in enumerate(schedule):
        print(f"Day {idx + 1}: {', '.join(cities)}")
else:
    print("No solution found")