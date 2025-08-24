def main():
    # Travel times
    travel = build_travel_times()

    # People constraints (24-hour times as strings)
    people_list = [
        Person("Charles",   "Bayview",          to_minutes("11:30"), to_minutes("14:30"), 45),
        Person("Robert",    "Sunset District",  to_minutes("16:45"), to_minutes("21:00"), 30),
        Person("Karen",     "Richmond District",to_minutes("19:15"), to_minutes("21:30"), 60),
        Person("Rebecca",   "Nob Hill",         to_minutes("16:15"), to_minutes("20:30"), 90),
        Person("Margaret",  "Chinatown",        to_minutes("14:15"), to_minutes("19:45"),120),
        Person("Patricia",  "Haight-Ashbury",   to_minutes("14:30"), to_minutes("20:30"), 45),
        Person("Mark",      "North Beach",      to_minutes("14:00"), to_minutes("18:30"),105),
        Person("Melissa",   "Russian Hill",     to_minutes("13:00"), to_minutes("19:45"), 30),
        Person("Laura",     "Embarcadero",      to_minutes("7:45"),  to_minutes("13:15"),105),
    ]
    name_to_idx = {p.name: i for i, p in enumerate(people_list)}

    start_loc = "Marina District"
    start_time = to_minutes("9:00")

    # Sort heuristic: try those with earliest latest-start first
    def latest_start(p: Person) -> int:
        return p.end - p.min_dur
    order = sorted(range(len(people_list)), key=lambda i: (latest_start(people_list[i]), people_list[i].end))

    best_solution = {
        "count": -1,
        "total_meeting": -1,
        "finish_time": 10**9,
        "travel_time": 10**9,
        "path": []  # list of tuples (name, location, start, end)
    }

    from functools import lru_cache

    @lru_cache(maxsize=None)
    def dfs(current_loc: str, current_time: int, remaining_mask: int) -> Tuple[int, int, int, int, Tuple[Tuple[str, str, int, int], ...]]:
        # Returns tuple: (best_count, total_meeting, finish_time, travel_time, path)
        best = (-1, -1, 10**9, 10**9, tuple())
        # Quick bound: if no remaining, return empties
        if remaining_mask == 0:
            return (0, 0, current_time, 0, tuple())

        # Upper bound pruning: count of remaining
        rem_count = bin(remaining_mask).count("1")
        # Try each candidate
        # Construct candidate indices in heuristic order
        cand_indices = [idx for idx in order if (remaining_mask >> idx) & 1]

        for idx in cand_indices:
            p = people_list[idx]
            t_travel = travel[current_loc][p.location]
            arrival = current_time + t_travel
            start = max(arrival, p.start)
            end = start + p.min_dur
            # Feasibility
            if end > p.end:
                continue

            new_mask = remaining_mask & ~(1 << idx)
            sub = dfs(p.location, end, new_mask)
            # Compose current result
            sub_count, sub_meet, sub_finish, sub_travel, sub_path = sub
            if sub_count >= 0:
                cur_count = 1 + sub_count
                cur_meet = p.min_dur + sub_meet
                cur_finish = sub_finish
                cur_travel = t_travel + sub_travel
                cur_path = ((p.name, p.location, start, end),) + sub_path

                # Update best with tie-breakers:
                # 1) more meetings
                # 2) if tie, more total meeting time
                # 3) if tie, earlier finish time
                # 4) if tie, less travel time
                if (cur_count > best[0] or
                    (cur_count == best[0] and cur_meet > best[1]) or
                    (cur_count == best[0] and cur_meet == best[1] and cur_finish < best[2]) or
                    (cur_count == best[0] and cur_meet == best[1] and cur_finish == best[2] and cur_travel < best[3])):
                    best = (cur_count, cur_meet, cur_finish, cur_travel, cur_path)

        # Option to stop scheduling now (end day) — but since objective is max count, skipping doesn't help unless no feasible next
        if best[0] < 0:
            # No feasible person remains
            return (0, 0, current_time, 0, tuple())
        return best

    remaining_mask = (1 << len(people_list)) - 1
    count, total_meeting, finish_time, travel_time_sum, path = dfs(start_loc, start_time, remaining_mask)

    # Build JSON itinerary
    itinerary = []
    for name, location, start, end in path:
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": name,
            "start_time": minutes_to_str(start),
            "end_time": minutes_to_str(end)
        })

    output = {"itinerary": itinerary}
    print(json.dumps(output, ensure_ascii=False))