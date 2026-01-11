import json
from itertools import permutations

def solve():
    # Cities and required days
    cities = {
        "Reykjavik": 2,
        "Stockholm": 3,
        "Tallinn": 5,
        "Oslo": 5,
        "Stuttgart": 5,
        "Split": 3,
        "Geneva": 2,
        "Porto": 3
    }
    
    # Direct flights (undirected)
    flights = {
        "Reykjavik": ["Stuttgart", "Stockholm", "Tallinn", "Oslo"],
        "Stockholm": ["Reykjavik", "Oslo", "Stuttgart", "Split", "Geneva"],
        "Oslo": ["Stockholm", "Split", "Geneva", "Porto", "Tallinn", "Reykjavik"],
        "Stuttgart": ["Reykjavik", "Stockholm", "Porto", "Split"],
        "Split": ["Oslo", "Stockholm", "Stuttgart", "Geneva"],
        "Geneva": ["Oslo", "Stockholm", "Porto", "Split"],
        "Porto": ["Stuttgart", "Oslo", "Geneva"],
        "Tallinn": ["Reykjavik", "Oslo"]
    }
    
    # Fixed constraints: day -> city
    fixed = {}
    for d in range(1, 3):  # Day 1-2
        fixed[d] = "Reykjavik"
    for d in range(19, 22):  # Day 19-21
        fixed[d] = "Porto"
    # Day 2-4 Stockholm
    for d in range(2, 5):
        if d in fixed and fixed[d] != "Stockholm":
            # Day 2 is fixed to Reykjavik, so must be travel day Reykjavik->Stockholm
            pass  # We'll handle by allowing two cities on day 2
        else:
            fixed[d] = "Stockholm"
    
    # We'll search over permutations of the 8 cities
    city_list = list(cities.keys())
    
    # We need to assign durations to each city in the permutation
    # such that sum of durations = 21 + (n_segments - 1) because overlaps
    # Actually simpler: We have 8 segments (one per city) with 7 overlaps (travel days)
    # So sum of (duration per segment) = 21 + 7 = 28.
    # Each segment's duration = stay_days + 1 if it's not the last? Wait, careful.
    
    # Let's model: We have sequence c1, c2, ..., c8.
    # Day count: start_day1 = 1, end_day1 = d1, start_day2 = d1, end_day2 = d1 + d2 - 1, etc.
    # where stay_days[i] = end_day_i - start_day_i + 1, but overlap day is counted in both.
    # For city i, total days counted = stay_days[i] except first/last? Let's implement search.
    
    def is_valid_sequence(seq, stays):
        # seq: list of cities in order
        # stays: list of durations in each segment (including overlap day with next)
        # Example: stays[0] = 3 means days 1,2,3 in seq[0], day 3 also in seq[1] if exists.
        day_city_map = {}
        # Build day_city_map: each day belongs to one or two cities
        day = 1
        for i in range(len(seq)):
            city = seq[i]
            duration = stays[i]
            for offset in range(duration):
                d = day + offset
                if d not in day_city_map:
                    day_city_map[d] = []
                day_city_map[d].append(city)
            day += duration - 1  # overlap next segment by 1 day
        
        # Check fixed constraints
        for d, req_city in fixed.items():
            if d not in day_city_map or req_city not in day_city_map[d]:
                return False
        
        # Check each city total days
        city_days_count = {city: 0 for city in cities}
        for d, city_list_day in day_city_map.items():
            for city in city_list_day:
                city_days_count[city] += 1
        
        for city, req in cities.items():
            if city_days_count[city] != req:
                return False
        
        # Check direct flights between consecutive cities in seq
        for i in range(len(seq) - 1):
            if seq[i+1] not in flights[seq[i]]:
                return False
        
        # Check total days = 21
        max_day = max(day_city_map.keys())
        if max_day != 21 or min(day_city_map.keys()) != 1:
            return False
        
        return day_city_map
    
    # Search over permutations and possible stays
    # stays are lengths of segments, each >= 2 except possibly first/last? Actually min = 1 if no travel? But travel needs overlap.
    # We know each stay_days[i] = cities[seq[i]] + (1 if i < len(seq)-1 else 0)?? Not exactly, because travel day might be extra.
    # Let's brute force small space: each stay >= cities[seq[i]].
    # Because a city's total days = stay_days[i] if it's first, else stay_days[i] - 1? Let's just brute.
    
    # We'll generate all permutations of cities
    for perm in permutations(city_list):
        # We can prune: first city must be Reykjavik (day 1 fixed)
        if perm[0] != "Reykjavik":
            continue
        # Last city must be Porto (day 21 fixed)
        if perm[-1] != "Porto":
            continue
        # Stockholm must be second city (because day 2-4 Stockholm and day 2 Reykjavik, so overlap day 2)
        if perm[1] != "Stockholm":
            continue
        
        # Now assign durations: we have 8 segments, total of stay_days sum = 28
        # stay_days[i] = cities[perm[i]] + extra, where extra is 1 if it has a next segment (overlap), but careful:
        # Actually, for city perm[i], its total days counted = stay_days[i] if i==0 else stay_days[i] - 1
        # Wait, that's messy. Let's brute small ranges.
        
        # We know stay_days[0] = cities["Reykjavik"] + 1? No, Reykjavik has 2 days total, and day 2 is overlap with Stockholm.
        # So stay_days[0] = 2 (day 1, day 2), day 2 is overlap.
        # stay_days[1] = cities["Stockholm"] + 1? Stockholm has 3 days total: day 2,3,4. But day 4 might be overlap with next.
        # So stay_days[1] = 3 (day 2,3,4), day 4 is overlap with next.
        # This is getting too heuristic. Let's do DFS for durations.
        
        # We'll DFS over segments to assign durations
        def dfs(segment_index, current_day, stays):
            if segment_index == len(perm):
                if current_day - 1 == 21:  # because current_day is next free day after last segment ends
                    day_map = is_valid_sequence(perm, stays)
                    if day_map:
                        return stays, day_map
                return None
            
            city = perm[segment_index]
            required = cities[city]
            # min_duration = required if segment_index == 0 else required + 1? Let's think:
            # For first city: duration >= required
            # For others: duration >= required + 1? Because one day is overlap with previous.
            # Actually, for city i (i>0), its total days = duration - 1 (since first day of its segment is overlap with previous city)
            # So duration - 1 = required => duration = required + 1.
            # For i=0: duration = required.
            # But wait, last city: duration = required (no next overlap).
            
            if segment_index == 0:
                min_dur = required
                max_dur = required  # fixed because day 1-2 Reykjavik
            elif segment_index == len(perm) - 1:
                min_dur = required + 1  # overlap with previous
                max_dur = required + 1
            else:
                min_dur = required + 1
                max_dur = required + 3  # some flexibility
            
            for dur in range(min_dur, max_dur + 1):
                # Check fixed day constraints for this segment's days
                ok = True
                for offset in range(dur):
                    d = current_day + offset
                    if d in fixed and fixed[d] != city:
                        # unless it's overlap day and fixed[d] is next city?
                        if offset == dur - 1 and segment_index < len(perm) - 1:
                            # overlap day, can be two cities
                            if fixed[d] != perm[segment_index + 1]:
                                # but must be one of them
                                if fixed[d] != city:
                                    ok = False
                                    break
                        else:
                            ok = False
                            break
                if not ok:
                    continue
                
                # Check direct flight to next city
                if segment_index < len(perm) - 1:
                    if perm[segment_index + 1] not in flights[city]:
                        continue
                
                res = dfs(segment_index + 1, current_day + dur - 1, stays + [dur])
                if res is not None:
                    return res
            return None
        
        res = dfs(0, 1, [])
        if res is not None:
            stays, day_map = res
            # Convert to itinerary format
            itinerary = []
            day = 1
            for i in range(len(perm)):
                city = perm[i]
                duration = stays[i]
                end_day = day + duration - 1
                itinerary.append({
                    "day_range": f"Day {day}-{end_day}",
                    "place": city
                })
                day = end_day  # overlap day for next
            return itinerary
    return None

def main():
    itinerary = solve()
    if itinerary is None:
        print('{"error": "No valid itinerary found"}')
        return
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()