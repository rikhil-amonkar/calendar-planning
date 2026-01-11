import itertools
import json

def find_best_itinerary():
    cities = ["Split", "Helsinki", "Reykjavik", "Vilnius", "Geneva"]
    required_days = {"Split": 2, "Helsinki": 2, "Reykjavik": 3, "Vilnius": 3, "Geneva": 6}
    
    direct_flights = {
        ("Split", "Helsinki"),
        ("Geneva", "Split"),
        ("Geneva", "Helsinki"),
        ("Helsinki", "Reykjavik"),
        ("Vilnius", "Helsinki"),
        ("Split", "Vilnius")
    }
    
    # Make it undirected
    def can_fly(a, b):
        return (a, b) in direct_flights or (b, a) in direct_flights
    
    # Fixed constraints
    fixed = {}
    for day in range(7, 10):  # days 7-9
        fixed[day] = "Vilnius"
    for day in range(10, 13):  # days 10-12
        fixed[day] = "Reykjavik"
    
    total_days = 12
    best_schedule = None
    best_score = float('inf')
    
    # We'll search over sequences of cities for days 1-12
    # Days 7-12 are fixed except travel overlaps possible
    # Actually, days 7-9 must be Vilnius, but we can be in other cities on those days if traveling
    # But fixed says must be in Vilnius on those days, so at least present there.
    
    # We'll brute force days 1-6 order, then days 7-12 fixed with possible multi-city on travel days.
    # Simplify: day-by-day city, but multi-city on travel days.
    # Let's just brute force permutations of city visits (not per day but sequence of stays).
    # Since small, we can brute force assignments for days 1-6.
    
    # Generate all possible city sequences for days 1-6
    possible = []
    for day1 in cities:
        for day2 in cities:
            for day3 in cities:
                for day4 in cities:
                    for day5 in cities:
                        for day6 in cities:
                            possible.append([day1, day2, day3, day4, day5, day6])
    
    # Limit to those with valid direct flights between consecutive days
    valid_seqs = []
    for seq in possible:
        ok = True
        for i in range(len(seq)-1):
            if not can_fly(seq[i], seq[i+1]):
                ok = False
                break
        if ok:
            valid_seqs.append(seq)
    
    # Now for each seq, build full 12-day with overlaps
    for seq in valid_seqs:
        # seq is days 1-6
        # days 7-9: Vilnius, but we can travel to Vilnius on day 7 from seq[6]
        # days 10-12: Reykjavik, but we can travel to Reykjavik on day 10 from Vilnius via Helsinki
        
        # Build day-by-day presence
        presence = {city: [0]*13 for city in cities}  # index 1..12
        
        # Days 1-6
        for day in range(1, 7):
            city = seq[day-1]
            presence[city][day] = 1
        
        # Day 7: start in seq[6] (city for day 6), fly to Vilnius if not already there
        day7_start = seq[5]
        if day7_start != "Vilnius":
            if not can_fly(day7_start, "Vilnius"):
                continue
            # travel day: present in both
            presence[day7_start][7] = 1
            presence["Vilnius"][7] = 1
        else:
            presence["Vilnius"][7] = 1
        
        # Days 8, 9 in Vilnius
        presence["Vilnius"][8] = 1
        presence["Vilnius"][9] = 1
        
        # Day 10: travel Vilnius -> Helsinki -> Reykjavik
        # Check direct flights: Vilnius->Helsinki yes, Helsinki->Reykjavik yes
        presence["Vilnius"][10] = 1  # morning in Vilnius
        presence["Helsinki"][10] = 1  # transit
        presence["Reykjavik"][10] = 1  # arrive
        
        # Days 11, 12 in Reykjavik
        presence["Reykjavik"][11] = 1
        presence["Reykjavik"][12] = 1
        
        # Count days per city
        total_city_days = {city: sum(presence[city]) for city in cities}
        
        # Score: sum of absolute differences from required days
        score = sum(abs(total_city_days[city] - required_days[city]) for city in cities)
        
        if score < best_score:
            best_score = score
            best_schedule = (seq, presence, total_city_days)
    
    if best_schedule is None:
        return {"error": "No feasible itinerary found"}
    
    seq, presence, total_city_days = best_schedule
    
    # Convert to itinerary format with day ranges
    itinerary = []
    day = 1
    while day <= 12:
        current = []
        for city in cities:
            if presence[city][day]:
                current.append(city)
        # Usually one city, but if multiple, we list as travel day
        place = current[0] if len(current) == 1 else f"Travel between {', '.join(current)}"
        start_day = day
        while day <= 12:
            next_day = []
            for city in cities:
                if presence[city][day+1] if day+1 <= 12 else False:
                    next_day.append(city)
            next_place = next_day[0] if len(next_day) == 1 else f"Travel between {', '.join(next_day)}"
            if next_place != place:
                break
            day += 1
        end_day = day
        if start_day == end_day:
            day_range_str = f"Day {start_day}"
        else:
            day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": place})
        day += 1
    
    # Compact consecutive same places
    compact = []
    for item in itinerary:
        if compact and compact[-1]["place"] == item["place"]:
            # Merge ranges
            last_range = compact[-1]["day_range"]
            if "-" in last_range:
                start = last_range.split("-")[0].replace("Day ", "")
                end = item["day_range"].split("-")[-1].replace("Day ", "")
                compact[-1]["day_range"] = f"Day {start}-{end}"
            else:
                # last was single day
                end = item["day_range"].split("-")[-1].replace("Day ", "")
                compact[-1]["day_range"] = f"Day {start}-{end}"
        else:
            compact.append(item)
    
    return {"itinerary": compact, "city_days": total_city_days, "score": best_score}

if __name__ == "__main__":
    result = find_best_itinerary()
    print(json.dumps({"itinerary": result["itinerary"]}, indent=2))