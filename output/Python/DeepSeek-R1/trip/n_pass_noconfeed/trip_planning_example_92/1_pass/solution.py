import itertools
import json

def main():
    total_days = 12
    city_days = {
        'Riga': 5,
        'Vilnius': 7,
        'Dublin': 2
    }
    graph = {
        'Dublin': ['Riga'],
        'Riga': ['Dublin', 'Vilnius'],
        'Vilnius': []
    }
    
    cities = list(city_days.keys())
    travel_days = sum(city_days.values()) - total_days
    
    found = False
    valid_order = None
    for perm in itertools.permutations(cities):
        if len(perm) < 3:
            continue
        if perm[1] in graph.get(perm[0], []) and perm[2] in graph.get(perm[1], []):
            A_end = city_days[perm[0]]
            B_end = A_end + city_days[perm[1]] - 1
            C_end = total_days
            if C_end - B_end + 1 == city_days[perm[2]]:
                found = True
                valid_order = perm
                break
    
    if found:
        A, B, C = valid_order
        A_end = city_days[A]
        B_end = A_end + city_days[B] - 1
        C_end = total_days
        itinerary = [
            {"day_range": f"Day 1-{A_end}", "place": A},
            {"day_range": f"Day {A_end}-{B_end}", "place": B},
            {"day_range": f"Day {B_end}-{C_end}", "place": C}
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No valid itinerary found"}))

if __name__ == "__main__":
    main()