from z3 import *

def main():
    s = Solver()
    cities = {
        'Amsterdam': 0,
        'Vienna': 1,
        'Santorini': 2,
        'Lyon': 3
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 14

    # Each day is assigned to a city (0-3)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 3)

    # Total days per city: Amsterdam(3), Vienna(7), Santorini(4), Lyon(3)
    totals = [3, 7, 4, 3]
    for city_code in range(4):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed date constraints (0-based days)
    # Amsterdam must be days 8-10 (1-based days 9-11)
    for i in [8, 9, 10]:
        s.add(day_city[i] == cities['Amsterdam'])
    # Lyon must be days 6-8 (1-based days 7-9)
    for i in [6, 7, 8]:
        s.add(day_city[i] == cities['Lyon'])

    # Direct flights between consecutive days (including staying in the same city)
    direct_flights = {
        0: [0, 1, 2, 3],  # Amsterdam connections
        1: [1, 0, 3, 2],   # Vienna connections
        2: [2, 1, 0],      # Santorini connections
        3: [3, 1, 0]       # Lyon connections
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        allowed = direct_flights.get(current, [current])
        s.add(Or([next_c == nc for nc in allowed]))

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