from z3 import *

def main():
    s = Solver()
    cities = {
        'Split': 0,
        'Helsinki': 1,
        'Reykjavik': 2,
        'Vilnius': 3,
        'Geneva': 4
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 12

    # Assign each day to a city (0-4)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 4)

    # Total days per city constraints
    totals = [2, 2, 3, 3, 6]
    for city_code in range(5):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Reykjavik days (1-based 10-12 → 0-based 9-11)
    for i in [9, 10, 11]:
        s.add(day_city[i] == cities['Reykjavik'])
    # Fixed Vilnius days (1-based 7-9 → 0-based 6-8)
    for i in [6, 7, 8]:
        s.add(day_city[i] == cities['Vilnius'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 1, 4, 3],        # Split can stay or fly to Helsinki, Geneva, Vilnius
        1: [1, 0, 4, 2, 3],     # Helsinki can stay or fly to Split, Geneva, Reykjavik, Vilnius
        2: [2, 1],              # Reykjavik can stay or fly to Helsinki
        3: [3, 0, 1],           # Vilnius can stay or fly to Split, Helsinki
        4: [4, 0, 1]            # Geneva can stay or fly to Split, Helsinki
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