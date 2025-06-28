import json

def main():
    total_days = 26
    cities = {
        "Prague": {"days": 3, "constraint": (1, 3)},
        "Warsaw": {"days": 4, "constraint": (20, 23)},
        "Dublin": {"days": 3, "constraint": None},
        "Athens": {"days": 3, "constraint": None},
        "Vilnius": {"days": 4, "constraint": None},
        "Porto": {"days": 5, "constraint": (16, 20)},
        "London": {"days": 3, "constraint": (3, 5)},
        "Seville": {"days": 2, "constraint": None},
        "Lisbon": {"days": 5, "constraint": (5, 9)},
        "Dubrovnik": {"days": 3, "constraint": None}
    }

    direct_flights = [
        ("Warsaw", "Vilnius"),
        ("Prague", "Athens"),
        ("London", "Lisbon"),
        ("Lisbon", "Porto"),
        ("Prague", "Lisbon"),
        ("London", "Dublin"),
        ("Athens", "Vilnius"),
        ("Athens", "Dublin"),
        ("Prague", "London"),
        ("London", "Warsaw"),
        ("Dublin", "Seville"),
        ("Seville", "Porto"),
        ("Lisbon", "Athens"),
        ("Dublin", "Porto"),
        ("Athens", "Warsaw"),
        ("Lisbon", "Warsaw"),
        ("Porto", "Warsaw"),
        ("Prague", "Warsaw"),
        ("Prague", "Dublin"),
        ("Athens", "Dubrovnik"),
        ("Lisbon", "Dublin"),
        ("Dubrovnik", "Dublin"),
        ("Lisbon", "Seville"),
        ("London", "Athens")
    ]

    city_sequence = [
        ("Prague", 1, 3),
        ("London", 3, 5),
        ("Lisbon", 5, 9),
        ("Athens", 9, 11),
        ("Dubrovnik", 11, 13),
        ("Dublin", 13, 15),
        ("Seville", 15, 16),
        ("Porto", 16, 20),
        ("Warsaw", 20, 23),
        ("Vilnius", 23, 26)
    ]

    graph = {}
    for city1, city2 in direct_flights:
        if city1 not in graph:
            graph[city1] = set()
        graph[city1].add(city2)
        if city2 not in graph:
            graph[city2] = set()
        graph[city2].add(city1)
    
    for i in range(len(city_sequence) - 1):
        city1 = city_sequence[i][0]
        city2 = city_sequence[i+1][0]
        if city1 in graph and city2 in graph[city1]:
            continue
        elif city2 in graph and city1 in graph[city2]:
            continue
        else:
            raise ValueError(f"No direct flight found between {city1} and {city2}")

    for city, start, end in city_sequence:
        constraint = cities[city].get("constraint")
        if constraint is not None:
            a, b = constraint
            if end < a or start > b:
                raise ValueError(f"Constraint for {city} not satisfied: stay from {start} to {end} not within [{a}, {b}]")

    for city, start, end in city_sequence:
        required_days = cities[city]["days"]
        actual_days = end - start + 1
        if actual_days != required_days:
            raise ValueError(f"City {city} has {actual_days} days, but requires {required_days} days")

    if city_sequence[-1][2] != total_days:
        raise ValueError(f"Last day is {city_sequence[-1][2]}, but should be {total_days}")

    itinerary_list = []
    for city, start, end in city_sequence:
        itinerary_list.append({
            "day_range": f"Day {start}-{end}",
            "place": city
        })

    result = {"itinerary": itinerary_list}
    print(json.dumps(result))

if __name__ == "__main__":
    main()