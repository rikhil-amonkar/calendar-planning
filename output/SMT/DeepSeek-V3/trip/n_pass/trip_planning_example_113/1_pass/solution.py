from z3 import *

def solve_itinerary():
    s = Solver()

    cities = ['Naples', 'Seville', 'Milan']
    city_codes = {c: i for i, c in enumerate(cities)}
    n_days = 12

    day_city = [Int(f'day_{i}_city') for i in range(1, n_days + 1)]

    for day in day_city:
        s.add(Or([day == city_codes[c] for c in cities]))

    s.add(Sum([If(day == city_codes['Naples'], 1, 0) for day in day_city]) == 3)
    s.add(Sum([If(day == city_codes['Seville'], 1, 0) for day in day_city]) == 4)
    s.add(Sum([If(day == city_codes['Milan'], 1, 0) for day in day_city]) == 7)

    for i in range(9, 13):
        s.add(day_city[i-1] == city_codes['Seville'])

    for i in range(n_days - 1):
        current = day_city[i]
        next_c = day_city[i+1]
        s.add(Or(
            current == next_c,
            And(current == city_codes['Milan'], next_c == city_codes['Seville']),
            And(current == city_codes['Seville'], next_c == city_codes['Milan']),
            And(current == city_codes['Naples'], next_c == city_codes['Milan']),
            And(current == city_codes['Milan'], next_c == city_codes['Naples'])
        ))

    if s.check() == sat:
        model = s.model()
        itinerary_days = []
        for i in range(n_days):
            city_idx = model.evaluate(day_city[i]).as_long()
            itinerary_days.append(cities[city_idx])

        itinerary = []
        current_place = itinerary_days[0]
        start_day = 1

        for i in range(1, n_days):
            if itinerary_days[i] != itinerary_days[i-1]:
                flight_day = i + 1
                from_city = itinerary_days[i-1]
                to_city = itinerary_days[i]
                if start_day == i:
                    itinerary.append({"day_range": f"Day {start_day}", "place": from_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{i}", "place": from_city})
                itinerary.append({"day_range": f"Day {flight_day}", "place": from_city})
                itinerary.append({"day_range": f"Day {flight_day}", "place": to_city})
                start_day = flight_day
                current_place = to_city

        if start_day <= n_days:
            if start_day == n_days:
                itinerary.append({"day_range": f"Day {start_day}", "place": current_place})
            else:
                itinerary.append({"day_range": f"Day {start_day}-{n_days}", "place": current_place})

        return {"itinerary": itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
import json
print(json.dumps(result, indent=2))