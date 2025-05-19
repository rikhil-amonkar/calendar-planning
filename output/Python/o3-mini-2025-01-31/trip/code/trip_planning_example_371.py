import json

def plan_trip():
    # Total itinerary days and required days in each city (pure counts)
    total_days = 9
    required_days = {
        "Vienna": 2,
        "Nice": 2,
        "Stockholm": 5,
        "Split": 3
    }
    
    # The constraints also require:
    # - A workshop in Vienna between day 1 and day 2, so Vienna must be visited at the start.
    # - A conference in Split on day 7 and day 9, so Split must include those days.
    # - You only take direct flights.
    # One viable direct flight route given available connections is:
    #   Vienna -> Nice -> Stockholm -> Split
    #
    # On a flight day, if you fly from city A to city B on day X,
    # that day counts as a day in both city A and city B.
    # We need 4 city visits (Vienna, Nice, Stockholm, Split) with a total of 9 days.
    # If we sum the required days the total is 2 + 2 + 5 + 3 = 12 days.
    # Since the itinerary is 9 days, we must have 3 overlapping flight days.
    #
    # We choose the following allocation:
    # - Vienna: Day 1-2 (2 days). (Workshop in Vienna is satisfied here.)
    #    Flight from Vienna to Nice happens on Day 2 (overlap).
    # - Nice: Day 2-3 (2 days). (Flight from Nice to Stockholm happens on Day 3.)
    # - Stockholm: Day 3-7 (5 days). (Flight from Stockholm to Split happens on Day 7.)
    # - Split: Day 7-9 (3 days). (Conference in Split on day 7 and day 9.)
    
    itinerary = []
    
    # Vienna segment: Days 1-2
    vienna_start = 1
    vienna_end = vienna_start + required_days["Vienna"] - 1  # 1 + 2 - 1 = 2
    itinerary.append({"day_range": f"{vienna_start}-{vienna_end}", "place": "Vienna"})
    
    # Nice segment: Flight on day 2 from Vienna to Nice (overlap day 2)
    nice_start = vienna_end  # Day 2 is counted in both Vienna and Nice
    nice_end = nice_start + required_days["Nice"] - 1  # 2 + 2 - 1 = 3
    itinerary.append({"day_range": f"{nice_start}-{nice_end}", "place": "Nice"})
    
    # Stockholm segment: Flight on day 3 from Nice to Stockholm (day 3 is overlapping)
    stockholm_start = nice_end  # Day 3 overlap
    stockholm_end = stockholm_start + required_days["Stockholm"] - 1  # 3 + 5 - 1 = 7
    itinerary.append({"day_range": f"{stockholm_start}-{stockholm_end}", "place": "Stockholm"})
    
    # Split segment: Flight on day 7 from Stockholm to Split (day 7 is overlapping)
    split_start = stockholm_end  # Day 7 overlap
    split_end = split_start + required_days["Split"] - 1  # 7 + 3 - 1 = 9
    itinerary.append({"day_range": f"{split_start}-{split_end}", "place": "Split"})
    
    return itinerary

if __name__ == "__main__":
    plan = plan_trip()
    print(json.dumps(plan))