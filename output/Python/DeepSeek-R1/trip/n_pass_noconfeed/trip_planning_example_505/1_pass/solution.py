import json

def main():
    cities = ['Prague', 'Stuttgart', 'Split', 'Krakow', 'Florence']
    direct_flights = {
        'Stuttgart': ['Split', 'Krakow'],
        'Prague': ['Florence', 'Split', 'Krakow'],
        'Florence': ['Prague'],
        'Split': ['Stuttgart', 'Krakow', 'Prague'],
        'Krakow': ['Stuttgart', 'Split', 'Prague']
    }
    required_counts = {
        'Prague': 4,
        'Stuttgart': 2,
        'Split': 2,
        'Krakow': 2,
        'Florence': 2
    }

    def dfs(day, current_city, counts, itinerary):
        if day == 9:
            for city in cities:
                if counts.get(city, 0) != required_counts[city]:
                    return None
            return itinerary[:]
        
        actions = ['stay'] + direct_flights[current_city]
        for act in actions:
            new_set = None
            new_current = current_city
            if act == 'stay':
                new_set = [current_city]
                counts[current_city] = counts.get(current_city, 0) + 1
            else:
                new_set = [current_city, act]
                new_current = act
                counts[current_city] = counts.get(current_city, 0) + 1
                counts[act] = counts.get(act, 0) + 1

            valid = True
            if day == 2:
                if 'Stuttgart' not in new_set:
                    valid = False
            elif day == 3:
                if 'Stuttgart' not in new_set or 'Split' not in new_set:
                    valid = False
            elif day == 4:
                if 'Split' not in new_set:
                    valid = False

            if not valid:
                if act == 'stay':
                    counts[current_city] = counts.get(current_city, 0) - 1
                else:
                    counts[current_city] = counts.get(current_city, 0) - 1
                    counts[act] = counts.get(act, 0) - 1
                continue

            itinerary.append(new_set)
            found = dfs(day + 1, new_current, counts, itinerary)
            if found is not None:
                return found
            itinerary.pop()
            if act == 'stay':
                counts[current_city] = counts.get(current_city, 0) - 1
            else:
                counts[current_city] = counts.get(current_city, 0) - 1
                counts[act] = counts.get(act, 0) - 1
        return None

    solution = None
    for start_city in cities:
        if solution:
            break
        for act in ['stay'] + direct_flights[start_city]:
            counts_trial = {city: 0 for city in cities}
            itinerary_trial = []
            if act == 'stay':
                new_set = [start_city]
                counts_trial[start_city] = 1
                new_current = start_city
            else:
                new_set = [start_city, act]
                counts_trial[start_city] = 1
                counts_trial[act] = 1
                new_current = act
            itinerary_trial.append(new_set)
            res = dfs(2, new_current, counts_trial, itinerary_trial)
            if res is not None:
                solution = res
                break

    if solution is None:
        result_json = json.dumps({"itinerary": []})
        print(result_json)
        return

    segments = []
    i = 0
    n = len(solution)
    while i < n:
        s = solution[i]
        if len(s) == 1:
            city = s[0]
            j = i + 1
            while j < n and len(solution[j]) == 1 and solution[j][0] == city:
                j += 1
            start_day = i + 1
            end_day = j
            segments.append((start_day, end_day, city))
            i = j
        else:
            s_str = s[0] + " and " + s[1]
            segments.append((i + 1, i + 1, s_str))
            i += 1

    itinerary_output = []
    for seg in segments:
        start, end, place = seg
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_output.append({"day_range": day_range_str, "place": place})
    
    result = {"itinerary": itinerary_output}
    print(json.dumps(result))

if __name__ == "__main__":
    main()