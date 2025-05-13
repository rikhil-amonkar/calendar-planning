from z3 import *

def main():
    s = Solver()
    cities = {
        'Naples': 0,
        'Seville': 1,
        'Milan': 2
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 12

    # Assign each day to a city (0-2)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 2)

    # Total days per city constraints (Naples:3, Seville:4, Milan:7)
    totals = [3, 4, 7]
    for city_code in range(3):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Seville days (1-based 9-12 → 0-based 8-11)
    for i in range(8, 12):
        s.add(day_city[i] == cities['Seville'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 2],       # Naples can stay or fly to Milan
        1: [1, 2],       # Seville can stay or fly to Milan
        2: [2, 0, 1]    # Milan can stay, fly to Naples or Seville
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