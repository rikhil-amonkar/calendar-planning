import json
from itertools import permutations

graph = {
    "Porto": ["Paris", "Munich", "Nice", "Warsaw", "Vienna"],
    "Paris": ["Warsaw", "Florence", "Vienna", "Nice", "Munich", "Porto"],
    "Florence": ["Vienna", "Munich", "Paris"],
    "Munich": ["Vienna", "Warsaw", "Nice", "Florence", "Paris", "Porto"],
    "Nice": ["Vienna", "Warsaw", "Porto", "Paris", "Munich"],
    "Warsaw": ["Paris", "Vienna", "Munich", "Nice", "Porto"],
    "Vienna": ["Florence", "Munich", "Porto", "Warsaw", "Nice", "Paris"]
}

gap2_city = "Florence"
non_fixed_5day = ["Paris", "Munich", "Nice"]

found = False
assignment = None
for perm in permutations(non_fixed_5day):
    gap1_city = perm[0]
    gap3_city = perm[1]
    gap4_city = perm[2]
    if (gap1_city in graph["Porto"] and
        gap2_city in graph[gap1_city] and
        gap3_city in graph[gap2_city] and
        gap3_city in graph["Warsaw"] and
        gap4_city in graph["Warsaw"] and
        gap4_city in graph["Vienna"]):
        assignment = (gap1_city, gap2_city, gap3_city, gap4_city)
        found = True
        break

if not found:
    assignment = ("Paris", "Florence", "Munich", "Nice")

itinerary_segments = [
    ("Porto", 1, 3),
    (assignment[0], 3, 7),
    (assignment[1], 7, 9),
    (assignment[2], 9, 13),
    ("Warsaw", 13, 15),
    (assignment[3], 15, 19),
    ("Vienna", 19, 20)
]

itinerary = []
for seg in itinerary_segments:
    place, start, end = seg
    day_range_str = f"Day {start}-{end}"
    itinerary.append({"day_range": day_range_str, "place": place})

result = {"itinerary": itinerary}
print(json.dumps(result))