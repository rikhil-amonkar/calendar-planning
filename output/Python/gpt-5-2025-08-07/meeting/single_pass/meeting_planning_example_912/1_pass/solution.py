def main():
    travel = build_travel_times()

    # Input variables (constraints)
    start_location = 'Union Square'
    start_time = time_to_minutes('9:00')

    people = [
        {'name': 'Kimberly', 'location': 'Presidio', 'start': time_to_minutes('15:30'), 'end': time_to_minutes('16:00'), 'min_duration': 15},
        {'name': 'Elizabeth', 'location': 'Alamo Square', 'start': time_to_minutes('19:15'), 'end': time_to_minutes('20:15'), 'min_duration': 15},
        {'name': 'Joshua', 'location': 'Marina District', 'start': time_to_minutes('10:30'), 'end': time_to_minutes('14:15'), 'min_duration': 45},
        {'name': 'Sandra', 'location': 'Financial District', 'start': time_to_minutes('19:30'), 'end': time_to_minutes('20:15'), 'min_duration': 45},
        {'name': 'Kenneth', 'location': 'Nob Hill', 'start': time_to_minutes('12:45'), 'end': time_to_minutes('21:45'), 'min_duration': 30},
        {'name': 'Betty', 'location': 'Sunset District', 'start': time_to_minutes('14:00'), 'end': time_to_minutes('19:00'), 'min_duration': 60},
        {'name': 'Deborah', 'location': 'Chinatown', 'start': time_to_minutes('17:15'), 'end': time_to_minutes('20:30'), 'min_duration': 15},
        {'name': 'Barbara', 'location': 'Russian Hill', 'start': time_to_minutes('17:30'), 'end': time_to_minutes('21:15'), 'min_duration': 120},
        {'name': 'Steven', 'location': 'North Beach', 'start': time_to_minutes('17:45'), 'end': time_to_minutes('20:45'), 'min_duration': 90},
        {'name': 'Daniel', 'location': 'Haight-Ashbury', 'start': time_to_minutes('18:30'), 'end': time_to_minutes('18:45'), 'min_duration': 15},
    ]

    name_to_idx = {p['name']: i for i, p in enumerate(people)}

    # Precompute to speed up
    def feasible_meeting(cur_loc, cur_time, person):
        loc = person['location']
        if cur_loc not in travel or loc not in travel[cur_loc]:
            return None
        arrive = cur_time + travel[cur_loc][loc]
        start = max(arrive, person['start'])
        end = start + person['min_duration']
        if end <= person['end']:
            return (start, end)
        return None

    # Order heuristic: try earlier-ending windows first
    order_indices = list(range(len(people)))
    # But keep dynamic sorting per state by window end
    def candidates(cur_loc, cur_time, visited_mask):
        cands = []
        for i, person in enumerate(people):
            if (visited_mask >> i) & 1:
                continue
            feas = feasible_meeting(cur_loc, cur_time, person)
            if feas is not None:
                start, end = feas
                cands.append((i, start, end))
        # sort primarily by end time, then by window end, then by duration descending (to schedule tight ones earlier)
        cands.sort(key=lambda x: (x[2], people[x[0]]['end'], -people[x[0]]['min_duration']))
        return cands

    from functools import lru_cache

    # Map location to index for caching (string is hashable but use int for compactness)
    locations = list(travel.keys())
    loc_index = {loc: idx for idx, loc in enumerate(locations)}

    @lru_cache(maxsize=None)
    def dfs(cur_loc_idx, cur_time, visited_mask):
        cur_loc = locations[cur_loc_idx]
        best = (0, 0, cur_time, [])  # (count, total_minutes, finish_time, itinerary_list)
        for i, start, end in candidates(cur_loc, cur_time, visited_mask):
            person = people[i]
            new_mask = visited_mask | (1 << i)
            child = dfs(loc_index[person['location']], end, new_mask)
            count = 1 + child[0]
            total_minutes = (end - start) + child[1]
            finish_time = child[2]  # child's finish time accounts for this meeting as we started it at 'end' time
            itinerary = [{
                'action': 'meet',
                'location': person['location'],
                'person': person['name'],
                'start_time': minutes_to_time(start),
                'end_time': minutes_to_time(end)
            }] + child[3]
            # Compare with current best: maximize (count, total_minutes), tie-breaker: earlier finish_time
            current_key = (count, total_minutes, -finish_time)
            best_key = (best[0], best[1], -best[2])
            if current_key > best_key:
                best = (count, total_minutes, finish_time, itinerary)
        return best

    best_solution = dfs(loc_index[start_location], start_time, 0)
    itinerary = best_solution[3]

    # Ensure itinerary is time-ordered (it should already be)
    itinerary.sort(key=lambda x: time_to_minutes(x['start_time']))

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))