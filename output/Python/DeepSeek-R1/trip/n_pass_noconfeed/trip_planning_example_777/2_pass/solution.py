from functools import lru_cache
import json

cities = ['Dublin', 'Tallinn', 'Riga', 'Reykjavik', 'Vienna', 'Helsinki']
city_index = {city: idx for idx, city in enumerate(cities)}
required_days = [5, 5, 3, 2, 2, 3]  # Corresponding to cities order

graph = {
    'Dublin': ['Tallinn', 'Riga', 'Vienna', 'Reykjavik', 'Helsinki'],
    'Tallinn': ['Dublin', 'Riga', 'Helsinki'],
    'Riga': ['Dublin', 'Vienna', 'Helsinki', 'Tallinn'],
    'Reykjavik': ['Dublin', 'Vienna', 'Helsinki'],
    'Vienna': ['Dublin', 'Riga', 'Reykjavik'],
    'Helsinki': ['Dublin', 'Riga', 'Reykjavik', 'Tallinn']
}

def main():
    for start_city in cities:
        initial_remaining = tuple(required_days)
        new_remaining = list(initial_remaining)
        idx = city_index[start_city]
        if new_remaining[idx] <= 0:
            continue
        new_remaining[idx] -= 1
        new_remaining = tuple(new_remaining)
        vienna2 = False  # (1 == 2) would be False, and (start_city=='Vienna' and False) is False
        vienna3 = False
        helsinki_event = False  # 1 not in [3,4,5]
        tallinn_event = False   # 1 not in [7,8,9,10,11]
        path_actions = dfs(start_city, 2, new_remaining, vienna2, vienna3, helsinki_event, tallinn_event)
        if path_actions is not None:
            itinerary = build_itinerary([start_city] + path_actions)
            output = {"itinerary": itinerary}
            print(json.dumps(output))
            return
    print(json.dumps({"itinerary": []}))

@lru_cache(maxsize=None)
def dfs(current_city, day, remaining_tuple, vienna2, vienna3, helsinki_event, tallinn_event):
    if day > 15:
        if all(r == 0 for r in remaining_tuple) and vienna2 and vienna3 and helsinki_event and tallinn_event:
            return []
        else:
            return None

    # Check if current city has remaining days, if not we cannot stay and for fly we require at least one day in current city
    idx_current = city_index[current_city]
    if remaining_tuple[idx_current] <= 0:
        # Cannot stay and cannot fly (because we are in current city at the start of the day and need to use one day)
        return None

    # Option 1: Stay in current city
    new_remaining_list = list(remaining_tuple)
    new_remaining_list[idx_current] -= 1
    new_remaining = tuple(new_remaining_list)
    cities_today = [current_city]
    new_vienna2, new_vienna3, new_helsinki_event, new_tallinn_event = update_events(day, cities_today, vienna2, vienna3, helsinki_event, tallinn_event)
    res_stay = dfs(current_city, day+1, new_remaining, new_vienna2, new_vienna3, new_helsinki_event, new_tallinn_event)
    if res_stay is not None:
        return [current_city] + res_stay

    # Option 2: Fly to a neighbor
    for next_city in graph[current_city]:
        if next_city == current_city:
            continue
        idx_next = city_index[next_city]
        if remaining_tuple[idx_next] <= 0:
            continue
        new_remaining_list = list(remaining_tuple)
        # We are spending the current day in two cities: current and next
        # So we need to decrement both
        new_remaining_list[idx_current] -= 1
        new_remaining_list[idx_next] -= 1
        # If after decrementing, current city becomes negative? We already checked it was at least 1, so it becomes 0 or more.
        # But we must check if next city becomes negative? We checked it was at least 1 so becomes 0 or more.
        new_remaining = tuple(new_remaining_list)
        cities_today = [current_city, next_city]
        new_vienna2, new_vienna3, new_helsinki_event, new_tallinn_event = update_events(day, cities_today, vienna2, vienna3, helsinki_event, tallinn_event)
        res_fly = dfs(next_city, day+1, new_remaining, new_vienna2, new_vienna3, new_helsinki_event, new_tallinn_event)
        if res_fly is not None:
            return [next_city] + res_fly

    return None

def update_events(day, cities_today, vienna2, vienna3, helsinki_event, tallinn_event):
    new_vienna2 = vienna2
    new_vienna3 = vienna3
    new_helsinki_event = helsinki_event
    new_tallinn_event = tallinn_event
    
    if day == 2 and 'Vienna' in cities_today:
        new_vienna2 = True
    if day == 3 and 'Vienna' in cities_today:
        new_vienna3 = True
    if not helsinki_event and day in [3,4,5] and 'Helsinki' in cities_today:
        new_helsinki_event = True
    if not tallinn_event and day in range(7,12) and 'Tallinn' in cities_today:
        new_tallinn_event = True
        
    return new_vienna2, new_vienna3, new_helsinki_event, new_tallinn_event

def build_itinerary(actions):
    days_per_city = {city: set() for city in cities}
    for day_idx, city in enumerate(actions, start=1):
        if day_idx > 15:
            break
        if day_idx == 1:
            days_per_city[city].add(day_idx)
        else:
            if actions[day_idx-1] == actions[day_idx-2]:
                days_per_city[city].add(day_idx)
            else:
                prev_city = actions[day_idx-2]
                days_per_city[prev_city].add(day_idx)
                days_per_city[city].add(day_idx)
    
    segments = []
    for city in cities:
        if not days_per_city[city]:
            continue
        sorted_days = sorted(days_per_city[city])
        start = sorted_days[0]
        end = start
        for i in range(1, len(sorted_days)):
            if sorted_days[i] == end + 1:
                end = sorted_days[i]
            else:
                segments.append((city, start, end))
                start = sorted_days[i]
                end = start
        segments.append((city, start, end))
    
    segments.sort(key=lambda x: x[1])
    itinerary_json = []
    for seg in segments:
        city, start, end = seg
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_json.append({"day_range": day_range_str, "place": city})
    
    return itinerary_json

if __name__ == '__main__':
    main()