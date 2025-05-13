from z3 import *

def main():
    s = Solver()
    cities = {
        'Split': 0,
        'Vilnius': 1,
        'Madrid': 2,
        'Santorini': 3
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 14

    # Assign each day to a city (0-3)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 3)

    # Total days per city constraints (Split:5, Vilnius:4, Madrid:6, Santorini:2)
    totals = [5, 4, 6, 2]
    for city_code in range(4):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Santorini days (1-based 13-14 → 0-based 12-13)
    s.add(day_city[12] == cities['Santorini'])
    s.add(day_city[13] == cities['Santorini'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 1, 2],  # Split can stay, fly to Vilnius or Madrid
        1: [1, 0],     # Vilnius can stay or fly to Split
        2: [2, 0, 3],  # Madrid can stay, fly to Split or Santorini
        3: [3, 2]      # Santorini can stay or fly to Madrid
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