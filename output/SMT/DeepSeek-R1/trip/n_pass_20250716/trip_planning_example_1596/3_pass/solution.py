itinerary = []

stays = [
    (1, 5, "Edinburgh"),
    (5, 9, "Barcelona"),
    (9, 13, "Budapest"),
    (13, 16, "Vienna"),
    (16, 18, "Stockholm"),
    (18, 20, "Munich"),
    (20, 20, "Warsaw"),
    (21, 24, "Riga"),
    (24, 25, "Bucharest"),
    (25, 29, "Warsaw"),
    (29, 32, "Krakow")
]

travels = [
    (5, "Edinburgh", "Barcelona"),
    (9, "Barcelona", "Budapest"),
    (13, "Budapest", "Vienna"),
    (16, "Vienna", "Stockholm"),
    (18, "Stockholm", "Munich"),
    (20, "Munich", "Warsaw"),
    (21, "Warsaw", "Riga"),
    (24, "Riga", "Bucharest"),
    (25, "Bucharest", "Warsaw"),
    (29, "Warsaw", "Krakow")
]

used_travel_indices = set()

for stay in stays:
    start, end, city = stay
    itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
    
    found_index = None
    for idx, travel in enumerate(travels):
        travel_day, from_city, to_city = travel
        if from_city == city and idx not in used_travel_indices:
            found_index = idx
            break
            
    if found_index is not None:
        travel_day, from_city, to_city = travels[found_index]
        itinerary.append({"day_range": f"Day {travel_day}", "place": from_city})
        itinerary.append({"day_range": f"Day {travel_day}", "place": to_city})
        used_travel_indices.add(found_index)

print({"itinerary": itinerary})