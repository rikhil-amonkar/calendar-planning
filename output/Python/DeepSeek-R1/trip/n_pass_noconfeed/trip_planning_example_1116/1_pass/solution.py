import json

def main():
    cities = [
        ("Bucharest", 2),
        ("Barcelona", 3),
        ("Split", 3),
        ("Stockholm", 4),
        ("Reykjavik", 5),
        ("Munich", 4),
        ("Oslo", 2),
        ("Frankfurt", 4)
    ]
    
    start = 1
    itinerary_list = []
    for city, days in cities:
        end = start + days - 1
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })
        start = end
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()