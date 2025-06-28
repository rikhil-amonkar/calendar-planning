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
    start_index = 0
    current_city = nightly_city[0]
    
    for i in range(1, len(nightly_city)):
        if nightly_city[i] != current_city:
            if start_index == i - 1:
                day_range_str = f"Day {start_index + 1}"
            else:
                day_range_str = f"Day {start_index + 1}-{i}"
            itinerary_list.append({"day_range": day_range_str, "place": current_city})
            start_index = i
            current_city = nightly_city[i]
    
    if start_index == len(nightly_city) - 1:
        day_range_str = f"Day {start_index + 1}"
    else:
        day_range_str = f"Day {start_index + 1}-{len(nightly_city)}"
    itinerary_list.append({"day_range": day_range_str, "place": current_city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()