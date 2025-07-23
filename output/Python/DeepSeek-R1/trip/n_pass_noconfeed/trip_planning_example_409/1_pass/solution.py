import json

def main():
    timeline = {}
    for day in range(1, 13):
        timeline[day] = []
    
    timeline[1].append('Helsinki')
    timeline[2].append('Helsinki')
    timeline[2].append('Zurich')
    timeline[3].append('Zurich')
    timeline[4].append('Zurich')
    timeline[4].append('Split')
    for day in range(5, 10):
        timeline[day].append('Split')
    timeline[10].append('Split')
    timeline[10].append('Hamburg')
    timeline[11].append('Hamburg')
    timeline[11].append('Bucharest')
    timeline[12].append('Bucharest')
    
    city_days = {}
    for day, cities in timeline.items():
        for city in cities:
            if city not in city_days:
                city_days[city] = set()
            city_days[city].add(day)
    
    sorted_cities = sorted(city_days.keys(), key=lambda c: min(city_days[c]))
    
    itinerary_list = []
    for city in sorted_cities:
        days = sorted(city_days[city])
        first_day = days[0]
        last_day = days[-1]
        if first_day == last_day:
            day_range_str = f"Day {first_day}"
        else:
            day_range_str = f"Day {first_day}-{last_day}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": city
        })
    
    result = {
        "itinerary": itinerary_list
    }
    print(json.dumps(result))

if __name__ == "__main__":
    main()