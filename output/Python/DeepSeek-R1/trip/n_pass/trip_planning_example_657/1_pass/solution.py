import json

def main():
    itinerary_list = []
    start = 1
    cities = [("Valencia", 4), ("Naples", 4), ("Manchester", 4), ("Oslo", 3), ("Vilnius", 1)]
    
    for i in range(4):
        city, block = cities[i]
        end = start + block - 1
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        start = end
    
    city, block = cities[4]
    end = start + block
    itinerary_list.append({
        "day_range": f"Day {start}-{end}",
        "place": city
    })
    start_frank = end
    end_frank = start_frank + 3
    itinerary_list.append({
        "day_range": f"Day {start_frank}-{end_frank}",
        "place": "Frankfurt"
    })
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()