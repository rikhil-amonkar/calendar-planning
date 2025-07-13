from z3 import *

def solve_itinerary():
    s = Solver()

    Mykonos, Budapest, Hamburg = 1, 2, 3
    city_names = {Mykonos: "Mykonos", Budapest: "Budapest", Hamburg: "Hamburg"}

    days = 9
    day_city = [Int(f"day_{i}_city") for i in range(1, days + 1)]

    for i in range(days):
        s.add(Or(day_city[i] == Mykonos, day_city[i] == Budapest, day_city[i] == Hamburg))

    s.add(day_city[3] == Mykonos)  # day 4
    s.add(day_city[8] == Mykonos)   # day 9

    total_mykonos = Sum([If(day_city[i] == Mykonos, 1, 0) for i in range(days)])
    total_budapest = Sum([If(day_city[i] == Budapest, 1, 0) for i in range(days)])
    total_hamburg = Sum([If(day_city[i] == Hamburg, 1, 0) for i in range(days)])

    s.add(total_mykonos == 6)
    s.add(total_budapest == 3)
    s.add(total_hamburg == 2)

    for i in range(days - 1):
        current = day_city[i]
        next_ = day_city[i + 1]
        s.add(Or(
            current == next_,
            And(current == Budapest, next_ == Mykonos),
            And(current == Mykonos, next_ == Budapest),
            And(current == Hamburg, next_ == Budapest),
            And(current == Budapest, next_ == Hamburg)
        ))

    if s.check() == sat:
        model = s.model()
        sequence = []
        for i in range(days):
            city_code = model.evaluate(day_city[i]).as_long()
            sequence.append(city_names[city_code])

        itinerary = []
        current_city = sequence[0]
        start_day = 1

        for day in range(1, days + 1):
            if day == days:
                next_city = None
            else:
                next_city = sequence[day]

            if day < days and sequence[day] != current_city:
                # Add the stay up to day-1
                if start_day == day:
                    itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                else:
                    itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})
                # Add the transition day
                itinerary.append({"day_range": f"Day {day + 1}", "place": current_city})
                itinerary.append({"day_range": f"Day {day + 1}", "place": sequence[day]})
                current_city = sequence[day]
                start_day = day + 2
            elif day == days:
                if start_day <= day:
                    if start_day == day:
                        itinerary.append({"day_range": f"Day {start_day}", "place": current_city})
                    else:
                        itinerary.append({"day_range": f"Day {start_day}-{day}", "place": current_city})

        # Post-process to merge consecutive same-city entries
        merged_itinerary = []
        i = 0
        while i < len(itinerary):
            current = itinerary[i]
            if i + 1 < len(itinerary) and itinerary[i+1]['place'] == current['place']:
                # Merge the day ranges
                current_days = current['day_range'].replace("Day ", "").split('-')
                start = int(current_days[0])
                if len(current_days) == 1:
                    end = start
                else:
                    end = int(current_days[1])
                next_days = itinerary[i+1]['day_range'].replace("Day ", "").split('-')
                next_start = int(next_days[0])
                if len(next_days) == 1:
                    next_end = next_start
                else:
                    next_end = int(next_days[1])
                new_start = min(start, next_start)
                new_end = max(end, next_end)
                merged = {"day_range": f"Day {new_start}-{new_end}", "place": current['place']}
                merged_itinerary.append(merged)
                i += 2
            else:
                merged_itinerary.append(current)
                i += 1

        return {"itinerary": merged_itinerary}
    else:
        return {"error": "No valid itinerary found"}

result = solve_itinerary()
print(result)