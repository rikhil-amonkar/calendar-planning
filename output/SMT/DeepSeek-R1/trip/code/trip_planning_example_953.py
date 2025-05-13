from z3 import *

def main():
    s = Solver()
    cities = {
        'Salzburg': 0,
        'Stockholm': 1,
        'Venice': 2,
        'Frankfurt': 3,
        'Florence': 4,
        'Barcelona': 5,
        'Stuttgart': 6
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 18

    # Assign each day to a city (0-6)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 6)

    # Total days per city constraints
    totals = [4, 2, 5, 4, 4, 2, 3]
    for city_code in range(7):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Venice days (1-based 1-5 → 0-based 0-4)
    for i in range(5):
        s.add(day_city[i] == cities['Venice'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 3],               # Salzburg
        1: [1, 3, 5, 6],         # Stockholm
        2: [2, 3, 5, 6],         # Venice
        3: [3, 0, 1, 4, 5, 6, 2], # Frankfurt
        4: [4, 3, 5],            # Florence
        5: [5, 1, 3, 4, 2, 6],   # Barcelona
        6: [6, 1, 3, 2, 5]       # Stuttgart
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