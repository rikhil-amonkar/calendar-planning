import json

def main():
    total_days = 16
    split_days = 5
    split_fixed_start = 7
    split_fixed_end = 11
    london_days = 7
    london_constraint_start = 1
    london_constraint_end = 7
    oslo_days = 2
    porto_days = 5
    direct_flights = [('London','Oslo'), ('Split','Oslo'), ('Oslo','Porto'), ('London','Split')]

    london_start = london_constraint_start
    london_end = london_start + london_days - 1
    if london_end > london_constraint_end:
        london_end = london_constraint_end

    split_start = split_fixed_start
    split_end = split_fixed_end

    oslo_start = split_end
    oslo_end = oslo_start + oslo_days - 1

    porto_start = oslo_end
    porto_end = porto_start + porto_days - 1

    cities_order = ["London", "Split", "Oslo", "Porto"]
    valid = True
    for i in range(len(cities_order) - 1):
        a, b = cities_order[i], cities_order[i+1]
        if (a, b) not in direct_flights and (b, a) not in direct_flights:
            valid = False
            break

    if not valid:
        result = {"itinerary": []}
    else:
        itinerary = [
            {"day_range": f"Day {london_start}-{london_end}", "place": "London"},
            {"day_range": f"Day {split_start}-{split_end}", "place": "Split"},
            {"day_range": f"Day {oslo_start}-{oslo_end}", "place": "Oslo"},
            {"day_range": f"Day {porto_start}-{porto_end}", "place": "Porto"}
        ]
        result = {"itinerary": itinerary}
    
    print(json.dumps(result))

if __name__ == "__main__":
    main()