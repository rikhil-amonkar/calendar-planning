# Auto-add symmetric travel times
for (a, b), time in list(travel_times.items()):
    if (b, a) not in travel_times:
        travel_times[(b, a)] = time