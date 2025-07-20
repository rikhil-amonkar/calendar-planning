import json

def main():
    total_days = 14
    cities = ['Vilnius', 'Split', 'Madrid', 'Santorini']
    days = [4, 5, 6, 2]
    
    starts = [0] * len(cities)
    starts[-1] = total_days - days[-1] + 1
    
    for i in range(len(cities)-2, -1, -1):
        starts[i] = starts[i+1] - days[i] + 1
        
    itinerary_list = []
    for i in range(len(cities)):
        if i == len(cities) - 1:
            end_day = total_days
        else:
            end_day = starts[i+1]
        day_range_str = f"Day {starts[i]}-{end_day}"
        itinerary_list.append({"day_range": day_range_str, "place": cities[i]})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()