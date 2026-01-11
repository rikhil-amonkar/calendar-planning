import itertools
import json

def flight_possible(city1, city2):
    flights = {
        ("Riga", "Oslo"),
        ("Rome", "Oslo"),
        ("Vienna", "Milan"),
        ("Vienna", "Vilnius"),
        ("Vienna", "Lisbon"),
        ("Riga", "Milan"),
        ("Lisbon", "Oslo"),
        ("Rome", "Riga"),
        ("Vienna", "Riga"),
        ("Vienna", "Rome"),
        ("Milan", "Oslo"),
        ("Vienna", "Oslo"),
        ("Vilnius", "Oslo"),
        ("Riga", "Vilnius"),
        ("Vilnius", "Milan"),
        ("Riga", "Lisbon"),
        ("Milan", "Lisbon"),
        ("Rome", "Lisbon")
    }
    return (city1, city2) in flights or (city2, city1) in flights

def check_itinerary(city_order, durations):
    # city_order: list of 7 cities, durations: list of 7 ints
    # Check flights between consecutive
    for i in range(len(city_order) - 1):
        if not flight_possible(city_order[i], city_order[i+1]):
            return False
    
    # Assign days
    # Start day 1
    day = 1
    stays = []
    for i in range(len(city_order)):
        length = durations[i]
        stays.append((city_order[i], day, day + length - 1))
        day += length - 1  # next stay starts on last day of current stay (overlap travel day)
    
    # Check total days = 15
    if stays[-1][2] != 15:
        return False
    
    # Check fixed constraints
    day_in_city = {}
    for city, start, end in stays:
        for d in range(start, end + 1):
            day_in_city[d] = city
    
    # Day 1 in Vienna
    if day_in_city.get(1) != "Vienna":
        return False
    # Day 4 in Vienna
    if day_in_city.get(4) != "Vienna":
        return False
    # Days 11-13 in Lisbon
    for d in range(11, 14):
        if day_in_city.get(d) != "Lisbon":
            return False
    # Days 13-15 in Oslo
    for d in range(13, 16):
        if day_in_city.get(d) != "Oslo":
            return False
    
    # Check each city total days = required
    city_days = {}
    for city, start, end in stays:
        city_days[city] = city_days.get(city, 0) + (end - start + 1)
    required = {"Vienna": 4, "Milan": 2, "Rome": 3, "Riga": 2, "Lisbon": 3, "Vilnius": 4, "Oslo": 3}
    for city, req in required.items():
        if city_days.get(city, 0) != req:
            return False
    
    return stays

def main():
    cities = ["Vienna", "Milan", "Rome", "Riga", "Lisbon", "Vilnius", "Oslo"]
    durations = [4, 2, 3, 2, 3, 4, 3]
    
    # We need to permute cities but keep durations fixed as above order? No, durations tied to cities.
    # Actually, we need to assign each city one duration from the list, but each city has fixed required days.
    # So we just permute cities and check if durations match required.
    # Required days per city:
    req_days = {"Vienna": 4, "Milan": 2, "Rome": 3, "Riga": 2, "Lisbon": 3, "Vilnius": 4, "Oslo": 3}
    
    # We'll generate permutations of cities
    for perm in itertools.permutations(cities):
        # durations for this permutation
        dur = [req_days[city] for city in perm]
        stays = check_itinerary(perm, dur)
        if stays:
            # Convert to output format
            itinerary = []
            for city, start, end in stays:
                if start == end:
                    day_range = f"Day {start}"
                else:
                    day_range = f"Day {start}-{end}"
                itinerary.append({"day_range": day_range, "place": city})
            
            result = {"itinerary": itinerary}
            print(json.dumps(result, indent=2))
            return
    
    print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()