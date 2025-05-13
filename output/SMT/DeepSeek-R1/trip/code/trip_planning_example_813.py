from z3 import *

def main():
    s = Solver()
    cities = {
        'Seville': 0,
        'Vilnius': 1,
        'Santorini': 2,
        'London': 3,
        'Stuttgart': 4,
        'Dublin': 5,
        'Frankfurt': 6
    }
    city_names = {v: k for k, v in cities.items()}
    days_total = 17

    # Each day is assigned to a city (0-6)
    day_city = [Int(f'day_{i+1}') for i in range(days_total)]
    for dc in day_city:
        s.add(dc >= 0, dc <= 6)

    # Total days per city
    totals = [0]*7
    totals[cities['Seville']] = 5
    totals[cities['Vilnius']] = 3
    totals[cities['Santorini']] = 2
    totals[cities['London']] = 2
    totals[cities['Stuttgart']] = 3
    totals[cities['Dublin']] = 3
    totals[cities['Frankfurt']] = 5

    for city_code in range(7):
        total = sum([If(dc == city_code, 1, 0) for dc in day_city])
        s.add(total == totals[city_code])

    # London on days 9 and 10 (1-based days 9,10 → 0-based indices 8,9)
    s.add(day_city[8] == cities['London'])
    s.add(day_city[9] == cities['London'])

    # Stuttgart days must be between day 7 and 9 (1-based → 0-based indices 6,7,8)
    stuttgart_code = cities['Stuttgart']
    for i in range(days_total):
        day_number = i + 1
        s.add(Implies(day_city[i] == stuttgart_code, And(day_number >=7, day_number <=9)))

    # Direct flights between consecutive days
    direct_flights = {
        cities['Seville']: [cities['Dublin']],
        cities['Vilnius']: [cities['Frankfurt']],
        cities['Santorini']: [cities['London'], cities['Dublin']],
        cities['London']: [cities['Frankfurt'], cities['Dublin'], cities['Santorini'], cities['Stuttgart']],
        cities['Stuttgart']: [cities['Frankfurt'], cities['London']],
        cities['Dublin']: [cities['Frankfurt'], cities['London'], cities['Seville'], cities['Santorini']],
        cities['Frankfurt']: [cities['Dublin'], cities['London'], cities['Vilnius'], cities['Stuttgart']]
    }

    for i in range(days_total - 1):
        current = day_city[i]
        next_c = day_city[i + 1]
        # Allow staying in the same city or flying via direct flight
        allowed = []
        for c in direct_flights:
            if current == c:
                allowed_next = direct_flights[c] + [c]
                allowed.append(Or([next_c == n for n in allowed_next]))
        s.add(Or(allowed))

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