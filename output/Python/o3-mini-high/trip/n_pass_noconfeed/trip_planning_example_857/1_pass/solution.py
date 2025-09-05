import itertools
import json

def main():
    total_days = 18
    # Required durations for each city.
    city_durations = {
        "Porto": 2,
        "Geneva": 3,
        "Mykonos": 3,
        "Manchester": 4,
        "Hamburg": 5,
        "Naples": 5,
        "Frankfurt": 2
    }
    
    # Build flight connection map.
    # For flights given as "A and B", assume bidirectional;
    # for "from Hamburg to Geneva" assume only Hamburg -> Geneva.
    flights = {
        "Hamburg": set(),
        "Frankfurt": set(),
        "Naples": set(),
        "Mykonos": set(),
        "Porto": set(),
        "Geneva": set(),
        "Manchester": set()
    }
    
    # 1. Hamburg and Frankfurt
    flights["Hamburg"].add("Frankfurt")
    flights["Frankfurt"].add("Hamburg")
    
    # 2. Naples and Mykonos
    flights["Naples"].add("Mykonos")
    flights["Mykonos"].add("Naples")
    
    # 3. Hamburg and Porto
    flights["Hamburg"].add("Porto")
    flights["Porto"].add("Hamburg")
    
    # 4. from Hamburg to Geneva (unidirectional)
    flights["Hamburg"].add("Geneva")
    # (Note: no Geneva->Hamburg edge)
    
    # 5. Mykonos and Geneva
    flights["Mykonos"].add("Geneva")
    flights["Geneva"].add("Mykonos")
    
    # 6. Frankfurt and Geneva
    flights["Frankfurt"].add("Geneva")
    flights["Geneva"].add("Frankfurt")
    
    # 7. Frankfurt and Porto
    flights["Frankfurt"].add("Porto")
    flights["Porto"].add("Frankfurt")
    
    # 8. Geneva and Porto
    flights["Geneva"].add("Porto")
    flights["Porto"].add("Geneva")
    
    # 9. Geneva and Manchester
    flights["Geneva"].add("Manchester")
    flights["Manchester"].add("Geneva")
    
    # 10. Naples and Manchester
    flights["Naples"].add("Manchester")
    flights["Manchester"].add("Naples")
    
    # 11. Frankfurt and Naples
    flights["Frankfurt"].add("Naples")
    flights["Naples"].add("Frankfurt")
    
    # 12. Frankfurt and Manchester
    flights["Frankfurt"].add("Manchester")
    flights["Manchester"].add("Frankfurt")
    
    # 13. Naples and Geneva
    flights["Naples"].add("Geneva")
    flights["Geneva"].add("Naples")
    
    # 14. Porto and Manchester
    flights["Porto"].add("Manchester")
    flights["Manchester"].add("Porto")
    
    # 15. Hamburg and Manchester
    flights["Hamburg"].add("Manchester")
    flights["Manchester"].add("Hamburg")
    
    # Event constraints:
    # - The Frankfurt annual show is from Day 5 to 6.
    #   With Frankfurt duration = 2 days, its segment must start on day 5.
    required_frankfurt_start = 5
    # - Meet a friend in Mykonos between Day 10 and 12.
    friend_meeting_window = (10, 12)
    # - Attend a wedding in Manchester between Day 15 and 18.
    wedding_window = (15, 18)
    
    # All cities
    cities = list(city_durations.keys())
    # We must visit all 7 cities exactly once.
    # Additionally, note:
    # - Total effective days = sum(durations) - (7-1) = 24 - 6 = 18.
    # - If flying on day X, that day counts in both cities.
    #
    # To satisfy the fixed-date events we deduce:
    # • Frankfurt must be in the itinerary at a position so that its start day is 5.
    #   Since start day for segment i (i>=1) equals sum_{j=0}^{i-1}(duration[j]) - (i-1),
    #   the simplest is to put Frankfurt in the 2nd position, so that start[1] = duration[first].
    #   Then duration[first] must equal 5.
    # • To cover the wedding window, Manchester should ideally be the last segment.
    #
    # Therefore, we restrict our search: 
    #   position 1 must be "Frankfurt",
    #   position 7 (index 6) must be "Manchester",
    #   and the first city (index 0) must have duration 5 (either "Hamburg" or "Naples").
    
    valid_itinerary = None
    for perm in itertools.permutations(cities):
        # Check fixed positions.
        if perm[1] != "Frankfurt":
            continue
        if perm[6] != "Manchester":
            continue
        if perm[0] not in {"Hamburg", "Naples"}:
            continue
        
        # Compute the itinerary timeline.
        # For the first city, start at day 1 and finish at: start + duration - 1.
        timeline = []  # Each element will be a tuple: (start_day, end_day) for that segment.
        start_day = 1
        for city in perm:
            dur = city_durations[city]
            end_day = start_day + dur - 1
            timeline.append((start_day, end_day))
            # Flight from current to next: they share the day of transition.
            start_day = end_day
        
        # The overall itinerary must exactly span total_days.
        if timeline[-1][1] != total_days:
            continue
        
        ok = True
        # Check event/date constraints:
        for city, (s, e) in zip(perm, timeline):
            if city == "Frankfurt":
                if s != required_frankfurt_start:
                    ok = False
                    break
            if city == "Mykonos":
                # Must overlap with friend meeting window.
                if e < friend_meeting_window[0] or s > friend_meeting_window[1]:
                    ok = False
                    break
            if city == "Manchester":
                # Must overlap with wedding window.
                if e < wedding_window[0] or s > wedding_window[1]:
                    ok = False
                    break
        if not ok:
            continue
        
        # Check direct flight connectivity between consecutive cities.
        for i in range(len(perm) - 1):
            departure = perm[i]
            arrival = perm[i+1]
            if arrival not in flights[departure]:
                ok = False
                break
        if not ok:
            continue
        
        # If we reached here, we have a valid itinerary.
        itinerary = []
        for city, (s, e) in zip(perm, timeline):
            itinerary.append({"day_range": f"Day {s}-{e}", "place": city})
        valid_itinerary = itinerary
        break

    result = {"itinerary": valid_itinerary if valid_itinerary is not None else []}
    print(json.dumps(result))

if __name__ == "__main__":
    main()