import json

def main():
    segments = [
        [("Florence", 5), ("Prague", 4), ("Tallinn", 5)],
        [("Frankfurt", 5)],
        [("Bucharest", 3), ("Zurich", 5), ("Venice", 5)]
    ]
    
    current_day = 1
    itinerary_list = []
    
    for segment in segments:
        for (city, duration) in segment:
            start = current_day
            end = start + duration - 1
            if start == end:
                day_range_str = f"Day {start}"
            else:
                day_range_str = f"Day {start}-{end}"
            itinerary_list.append({"day_range": day_range_str, "place": city})
            current_day = end
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()