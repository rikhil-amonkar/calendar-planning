import json

def main():
    # Input parameters and constraints
    total_days = 9
    mykonos_days_required = 6
    budapest_days_required = 3
    hamburg_days_required = 2
    conference_days = [4, 9]  # Must be in Mykonos on these days
    
    # Direct flight connections:
    #   Budapest <-> Mykonos
    #   Hamburg <-> Budapest
    # This forces an itinerary ordering: Hamburg -> Budapest -> Mykonos.
    #
    # Note: On a flight day from city A to city B the traveler is considered to be
    # in both cities.
    #
    # We construct an itinerary that meets:
    #   Hamburg for 2 days, Budapest for 3 days, Mykonos for 6 days (including day 4 and 9 as required)
    
    # One valid scheduling approach is:
    # Day 1: Start in Hamburg.
    # Day 2: Flight from Hamburg to Budapest: traveler is in Hamburg (completing Hamburg's 2 days: day 1 and 2)
    #         and in Budapest on day 2 (counting as the first Budapest day).
    # Day 3: Stay in Budapest.
    # Day 4: Flight from Budapest to Mykonos: traveler is in Budapest (thus Budapest counts day 4 as well)
    #         and in Mykonos on day 4 (and conference day 4 is satisfied).
    # Days 5-9: Remain in Mykonos, so that Mykonos counts days 4,5,6,7,8,9 (6 days total)
    #           and conference on day 9 is satisfied.
    #
    # Summaries:
    # Hamburg: Days 1-2 (2 days)
    # Budapest: Days 2-4 (3 days)
    # Mykonos: Days 4-9 (6 days)
    
    itinerary = []
    
    # Calculating Hamburg segment: start on day 1.
    hamburg_start = 1
    hamburg_end = hamburg_start + hamburg_days_required - 1  # 1 + 2 - 1 = 2
    itinerary.append({
        "day_range": f"{hamburg_start}-{hamburg_end}",
        "place": "Hamburg"
    })
    
    # Calculating Budapest segment: flight from Hamburg to Budapest happens on day 2.
    budapest_start = hamburg_end  # Overlap: day 2 is in both Hamburg and Budapest.
    budapest_end = budapest_start + budapest_days_required - 1  # 2 + 3 - 1 = 4
    itinerary.append({
        "day_range": f"{budapest_start}-{budapest_end}",
        "place": "Budapest"
    })
    
    # Calculating Mykonos segment: flight from Budapest to Mykonos happens on day 4.
    mykonos_start = budapest_end  # Overlap: day 4 is in both Budapest and Mykonos.
    mykonos_end = total_days             # Ends on day 9.
    itinerary.append({
        "day_range": f"{mykonos_start}-{mykonos_end}",
        "place": "Mykonos"
    })
    
    # Output itinerary as JSON with only day_range and place.
    print(json.dumps(itinerary))

if __name__ == '__main__':
    main()