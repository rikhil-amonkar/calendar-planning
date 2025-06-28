import json

def main():
    cities_in_order = ['Seville', 'Rome', 'Istanbul', 'Naples', 'Santorini']
    durations = [4, 3, 2, 7, 4]
    
    itinerary = []
    start_day = 1
    for i in range(len(cities_in_order)):
        city = cities_in_order[i]
        duration = durations[i]
        end_day = start_day + duration - 1
        day_range_str = f"Day {start_day}-{end_day}"
        itinerary.append({"day_range": day_range_str, "place": city})
        start_day = end_day
    
    result = {"itinerary": itinerary}
    print(json.dumps(result))

if __name__ == "__main__":
    main()