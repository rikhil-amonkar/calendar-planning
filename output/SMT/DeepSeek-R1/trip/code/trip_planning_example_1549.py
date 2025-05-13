from z3 import *

def main():
    s = Solver()
    cities = {
        'Prague': 0,
        'Tallinn': 1,
        'Warsaw': 2,
        'Porto': 3,
        'Naples': 4,
        'Milan': 5,
        'Lisbon': 6,
        'Santorini': 7,
        'Riga': 8,
        'Stockholm': 9
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 28

    # Assign each day to a city (0-9)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 9)

    # Total days per city constraints
    totals = [5, 3, 2, 3, 5, 3, 5, 5, 4, 2]
    for city_code in range(10):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Riga days (1-based 5-8 → 0-based 4-7)
    for i in range(4, 8):
        s.add(day_city[i] == cities['Riga'])
    # Fixed Tallinn days (1-based 18-20 → 0-based 17-19)
    for i in range(17, 20):
        s.add(day_city[i] == cities['Tallinn'])
    # Fixed Milan days (1-based 24-26 → 0-based 23-25)
    for i in range(23, 26):
        s.add(day_city[i] == cities['Milan'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 8, 1, 6, 5, 9, 2],  # Prague
        1: [1, 0, 2, 9],           # Tallinn
        2: [2, 4, 6, 8, 9, 3, 1, 5, 0],  # Warsaw
        3: [3, 6, 5, 2],            # Porto
        4: [4, 2, 5, 6, 7],         # Naples
        5: [5, 9, 8, 4, 3, 0, 6, 2, 7],  # Milan
        6: [6, 9, 2, 4, 8, 3, 0, 5],  # Lisbon
        7: [7, 5, 4],               # Santorini
        8: [8, 0, 5, 2, 1, 9, 6],  # Riga
        9: [9, 5, 7, 2, 8, 6, 0, 1]   # Stockholm
    }

    # Ensure consecutive days are connected by direct flights
    for i in range(days_total - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        allowed = direct_flights.get(current, [current])
        s.add(Or([next_day == a for a in allowed]))

    if s.check() == sat:
        model = s.model()
        schedule = [model.evaluate(day).as_long() for day in day_city]
        print("Day  City")
        for idx, city_code in enumerate(schedule):
            print(f"{idx + 1:3}  {city_names[city_code]}")
    else:
        print("No valid trip plan exists.")

if __name__ == "__main__":
    main()