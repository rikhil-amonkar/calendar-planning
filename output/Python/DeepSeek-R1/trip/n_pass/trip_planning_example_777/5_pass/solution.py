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
        city = nightly_city[i]
        start_day = i + 1
        j = i
        while j < n and nightly_city[j] == city:
            j += 1
        num_days = j - i
        end_day = start_day + num_days - 1
        
        if num_days == 1:
            day_range = f"Day {start_day}"
        else:
            day_range = f"Day {start_day}-{end_day}"
        
        itinerary_list.append({
            "day_range": day_range,
            "place": city
        })
        
        i = j
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()