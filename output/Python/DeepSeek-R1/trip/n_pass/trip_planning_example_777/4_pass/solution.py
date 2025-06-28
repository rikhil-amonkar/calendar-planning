import json

def main():
    nightly_city = [
        "Dublin",    # Day 1
        "Vienna",    # Day 2
        "Helsinki",  # Day 3
        "Helsinki",  # Day 4
        "Tallinn",   # Day 5
        "Tallinn",   # Day 6
        "Tallinn",   # Day 7
        "Tallinn",   # Day 8
        "Riga",      # Day 9
        "Riga",      # Day 10
        "Riga",      # Day 11
        "Reykjavik", # Day 12
        "Reykjavik", # Day 13
        "Reykjavik", # Day 14
        "Reykjavik"  # Day 15
    ]
    
    itinerary_list = []
    i = 0
    n = len(nightly_city)
    
    while i < n:
        j = i
        while j < n and nightly_city[j] == nightly_city[i]:
            j += 1
        
        start_day = i + 1
        end_day = j  # j is exclusive bound, last day is j (day number)
        
        if start_day == end_day:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day} to Day {end_day}"
        
        itinerary_list.append({
            "day_range": day_range,
            "place": nightly_city[i]
        })
        
        i = j
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()