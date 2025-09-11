import json

def main():
    cities = ["Nice", "Lyon", "Dublin", "Krakow", "Frankfurt"]
    days = [5, 4, 6, 7, 2]
    
    itinerary = []
    start = 1
    for i in range(len(cities)):
        end = start + days[i] - 1
        itinerary.append({
            "day_range": f"Day {start}-{end}",
            "place": cities[i]
        })
        start = end
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()