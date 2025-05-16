from z3 import *

# Define flight days between cities
flight1 = Int('flight1')  # Santorini to Vienna
flight2 = Int('flight2')  # Vienna to Madrid
flight3 = Int('flight3')  # Madrid to Seville
flight4 = Int('flight4')  # Seville to Valencia
flight5 = Int('flight5')  # Valencia to Krakow
flight6 = Int('flight6')  # Krakow to Frankfurt
flight7 = Int('flight7')  # Frankfurt to Bucharest
flight8 = Int('flight8')  # Bucharest to Riga
flight9 = Int('flight9')  # Riga to Tallinn

s = Solver()

# Constraints for flight days and durations
s.add(flight1 == 3)   # Santorini to Vienna on day 3 (Santorini days 1-3)
s.add(flight2 == 6)   # Vienna to Madrid on day 6 (Vienna days 3-6)
s.add(flight3 == 7)   # Madrid to Seville on day 7 (Madrid days 6-7)
s.add(flight4 == 8)   # Seville to Valencia on day 8 (Seville days 7-8)
s.add(flight5 == 11)  # Valencia to Krakow on day 11 (Valencia days 8-11)
s.add(flight6 == 15)  # Krakow to Frankfurt on day 15 (Krakow days 11-15)
s.add(flight7 == 18)  # Frankfurt to Bucharest on day 18 (Frankfurt days 15-18)
s.add(flight8 == 20)  # Bucharest to Riga on day 20 (Bucharest days 18-20)
s.add(flight9 == 23)  # Riga to Tallinn on day 23 (Riga days 20-23)

# Validate days in each city
s.add(flight1 - 1 == 3 - 1)          # Santorini: 3 days (1-3)
s.add(flight2 - flight1 + 1 == 4)    # Vienna: 4 days (3-6)
s.add(flight3 - flight2 + 1 == 2)    # Madrid: 2 days (6-7)
s.add(flight4 - flight3 + 1 == 2)    # Seville: 2 days (7-8)
s.add(flight5 - flight4 + 1 == 4)    # Valencia: 4 days (8-11)
s.add(flight6 - flight5 + 1 == 5)    # Krakow: 5 days (11-15)
s.add(flight7 - flight6 + 1 == 4)    # Frankfurt: 4 days (15-18)
s.add(flight8 - flight7 + 1 == 3)    # Bucharest: 3 days (18-20)
s.add(flight9 - flight8 + 1 == 4)    # Riga: 4 days (20-23)
s.add(27 - flight9 + 1 == 5)         # Tallinn: 5 days (23-27)

# Check direct flight connections
s.add(flight1 >= 1, flight1 <= 27)
s.add(flight2 >= flight1, flight2 <= 27)
s.add(flight3 >= flight2, flight3 <= 27)
s.add(flight4 >= flight3, flight4 <= 27)
s.add(flight5 >= flight4, flight5 <= 27)
s.add(flight6 >= flight5, flight6 <= 27)
s.add(flight7 >= flight6, flight7 <= 27)
s.add(flight8 >= flight7, flight8 <= 27)
s.add(flight9 >= flight8, flight9 <= 27)

if s.check() == sat:
    schedule = []
    for day in range(1, 28):
        cities = []
        # Santorini (1-3)
        if day < flight1:
            cities.append("Santorini")
        if day == flight1:
            cities.append("Santorini")
            cities.append("Vienna")
        # Vienna (3-6)
        if day > flight1 and day <= flight2:
            if day == flight2:
                cities.append("Vienna")
            else:
                cities.append("Vienna")
        # Madrid (6-7)
        if day > flight2 and day <= flight3:
            cities.append("Madrid")
        if day == flight3:
            cities.append("Madrid")
            cities.append("Seville")
        # Seville (7-8)
        if day > flight3 and day <= flight4:
            cities.append("Seville")
        if day == flight4:
            cities.append("Seville")
            cities.append("Valencia")
        # Valencia (8-11)
        if day > flight4 and day <= flight5:
            cities.append("Valencia")
        if day == flight5:
            cities.append("Valencia")
            cities.append("Krakow")
        # Krakow (11-15)
        if day > flight5 and day <= flight6:
            cities.append("Krakow")
        if day == flight6:
            cities.append("Krakow")
            cities.append("Frankfurt")
        # Frankfurt (15-18)
        if day > flight6 and day <= flight7:
            cities.append("Frankfurt")
        if day == flight7:
            cities.append("Frankfurt")
            cities.append("Bucharest")
        # Bucharest (18-20)
        if day > flight7 and day <= flight8:
            cities.append("Bucharest")
        if day == flight8:
            cities.append("Bucharest")
            cities.append("Riga")
        # Riga (20-23)
        if day > flight8 and day <= flight9:
            cities.append("Riga")
        if day == flight9:
            cities.append("Riga")
            cities.append("Tallinn")
        # Tallinn (23-27)
        if day > flight9:
            cities.append("Tallinn")
        schedule.append(cities)
    # Print the schedule
    for idx, cities in enumerate(schedule):
        print(f"Day {idx + 1}: {', '.join(cities)}")
else:
    print("No solution found")