from z3 import *

def main():
    s = Solver()
    cities = {
        'Helsinki': 0,
        'Valencia': 1,
        'Dubrovnik': 2,
        'Porto': 3,
        'Prague': 4,
        'Reykjavik': 5
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 18

    # Assign each day to a city (0-5)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 5)

    # Total days per city constraints
    totals = [4, 5, 4, 3, 3, 4]
    for city_code in range(6):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Porto days (1-based 16-18 → 0-based 15-17)
    for i in range(15, 18):
        s.add(day_city[i] == cities['Porto'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0,4,5,2],   # Helsinki
        1: [1,4,3],     # Valencia
        2: [2,0],       # Dubrovnik
        3: [3,1],       # Porto
        4: [4,0,1,5],   # Prague
        5: [5,0,4]      # Reykjavik
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