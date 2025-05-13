from z3 import *

def main():
    s = Solver()
    cities = {
        'London': 0,
        'Santorini': 1,
        'Istanbul': 2
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 10

    # Each day is assigned to a city (0-2)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 2)

    # Total days per city constraints
    totals = [3, 6, 3]
    for city_code in range(3):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Santorini must be days 4-9 (0-based, 1-based days 5-10)
    for i in range(4, 10):
        s.add(day_city[i] == cities['Santorini'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 1, 2],   # London can stay or go to Santorini/Istanbul
        1: [0, 1],       # Santorini can stay or go to London
        2: [0, 2]        # Istanbul can stay or go to London
    }

    # Ensure consecutive days are connected by direct flights
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