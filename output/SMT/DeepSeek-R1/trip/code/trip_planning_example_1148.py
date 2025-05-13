from z3 import *

def main():
    s = Solver()
    cities = {
        'Lisbon': 0,
        'Dubrovnik': 1,
        'Copenhagen': 2,
        'Prague': 3,
        'Tallinn': 4,
        'Stockholm': 5,
        'Split': 6,
        'Lyon': 7
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 19

    # Assign each day to a city (0-7)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 7)

    # Total days per city constraints
    totals = [2, 5, 5, 3, 2, 4, 3, 2]
    for city_code in range(8):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based)
    # Tallinn days 0-1
    s.add(day_city[0] == cities['Tallinn'])
    s.add(day_city[1] == cities['Tallinn'])
    # Lisbon days 3-4
    s.add(day_city[3] == cities['Lisbon'])
    s.add(day_city[4] == cities['Lisbon'])
    # Stockholm days 12-15
    for i in range(12, 16):
        s.add(day_city[i] == cities['Stockholm'])
    # Lyon days 17-18
    s.add(day_city[17] == cities['Lyon'])
    s.add(day_city[18] == cities['Lyon'])

    # Direct flights between consecutive days (including stay)
    direct_flights = {
        0: [0, 2, 3, 5, 7],   # Lisbon
        1: [1, 2, 5],          # Dubrovnik
        2: [0, 1, 2, 3, 4, 5, 6],  # Copenhagen
        3: [0, 2, 3, 4, 5, 6, 7],  # Prague
        4: [2, 3, 4, 5],       # Tallinn
        5: [0, 1, 2, 3, 4, 5, 6],  # Stockholm
        6: [2, 3, 5, 6, 7],    # Split
        7: [0, 3, 6, 7]        # Lyon
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_day = day_city[i + 1]
        allowed = direct_flights.get(current, [current])
        s.add(Or([next_day == nc for nc in allowed]))

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