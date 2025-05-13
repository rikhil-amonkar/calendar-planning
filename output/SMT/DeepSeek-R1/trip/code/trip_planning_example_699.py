from z3 import *

def main():
    s = Solver()
    cities = {
        'Mykonos': 0,
        'Reykjavik': 1,
        'Dublin': 2,
        'London': 3,
        'Helsinki': 4,
        'Hamburg': 5
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 16

    # Assign each day to a city (0-5)
    day_city = [Int(f'day_{i}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 5)

    # Total days per city constraints (Mykonos:3, Reykjavik:2, Dublin:5, London:5, Helsinki:4, Hamburg:2)
    totals = [3, 2, 5, 5, 4, 2]
    for city_code in range(6):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # Fixed Hamburg days (1-based 1-2 → 0-based 0-1)
    for i in [0, 1]:
        s.add(day_city[i] == cities['Hamburg'])
    # Fixed Dublin days (1-based 2-6 → 0-based 1-5)
    for i in range(1, 6):
        s.add(day_city[i] == cities['Dublin'])

    # Direct flights including staying in the same city
    direct_flights = {
        0: [0, 3],              # Mykonos: stay or fly to London
        1: [1, 4, 3, 2],        # Reykjavik: stay, Helsinki, London, Dublin
        2: [2, 3, 5, 4, 1],     # Dublin: stay, London, Hamburg, Helsinki, Reykjavik
        3: [3, 0, 2, 5, 1, 4],  # London: stay, Mykonos, Dublin, Hamburg, Reykjavik, Helsinki
        4: [4, 1, 2, 3, 5],     # Helsinki: stay, Reykjavik, Dublin, London, Hamburg
        5: [5, 2, 3, 4]         # Hamburg: stay, Dublin, London, Helsinki
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