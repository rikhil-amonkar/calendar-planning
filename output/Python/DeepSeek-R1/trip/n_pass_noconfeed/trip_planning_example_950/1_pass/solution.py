import json

def main():
    cities = ["Rome", "Mykonos", "Nice", "Riga", "Bucharest", "Munich", "Krakow"]
    durations = [4, 3, 3, 3, 4, 4, 2]
    
    itinerary_list = []
    current_start = 1
    for i in range(len(cities)):
        duration = durations[i]
        current_end = current_start + duration - 1
        day_range_str = f"Day {current_start}-{current_end}"
        itinerary_list.append({"day_range": day_range_str, "place": cities[i]})
        current_start = current_end
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()