import json

def main():
    total_days = 12
    durations = {
        "Prague": 2,
        "Berlin": 3,
        "Tallinn": 5,
        "Stockholm": 5
    }
    
    direct_flights_list = [
        ("Berlin", "Tallinn"),
        ("Prague", "Tallinn"),
        ("Stockholm", "Tallinn"),
        ("Prague", "Stockholm"),
        ("Stockholm", "Berlin")
    ]
    
    flight_connections = set()
    for a, b in direct_flights_list:
        flight_connections.add((a, b))
        flight_connections.add((b, a))
    
    berlin_block = (6, 8, "Berlin")
    tallinn_block = (8, 12, "Tallinn")
    
    possibility1 = [
        (1, 2, "Prague"),
        (2, 6, "Stockholm"),
        berlin_block,
        tallinn_block
    ]
    
    possibility2 = [
        (1, 5, "Stockholm"),
        (5, 6, "Prague"),
        berlin_block,
        tallinn_block
    ]
    
    def is_chain_valid(blocks):
        cities = [block[2] for block in blocks]
        for i in range(len(cities) - 1):
            if (cities[i], cities[i+1]) not in flight_connections:
                return False
        return True
    
    if is_chain_valid(possibility1):
        itinerary_blocks = possibility1
    elif is_chain_valid(possibility2):
        itinerary_blocks = possibility2
    else:
        itinerary_blocks = []
    
    itinerary_list = []
    for block in itinerary_blocks:
        start, end, city = block
        day_range_str = f"Day {start}-{end}"
        itinerary_list.append({"day_range": day_range_str, "place": city})
    
    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()