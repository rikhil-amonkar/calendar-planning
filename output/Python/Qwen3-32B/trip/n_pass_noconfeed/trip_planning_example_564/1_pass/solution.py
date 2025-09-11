import json

def main():
    cities = ['Seville', 'Rome', 'Istanbul', 'Naples', 'Santorini']
    flights = {
        'Rome': ['Santorini', 'Seville', 'Naples', 'Istanbul'],
        'Seville': ['Rome'],
        'Istanbul': ['Rome', 'Naples'],
        'Naples': ['Rome', 'Istanbul', 'Santorini'],
        'Santorini': ['Rome', 'Naples']
    }
    durations = {
        'Seville': 4,
        'Rome': 3,
        'Istanbul': 2,
        'Naples': 7,
        'Santorini': 4
    }

    def find_hamiltonian_paths():
        all_paths = []
        def backtrack(current_path):
            if len(current_path) == 5:
                all_paths.append(current_path.copy())
                return
            last_city = current_path[-1]
            for neighbor in flights[last_city]:
                if neighbor not in current_path:
                    current_path.append(neighbor)
                    backtrack(current_path)
                    current_path.pop()
        for city in cities:
            backtrack([city])
        return all_paths

    paths = find_hamiltonian_paths()

    for path in paths:
        days_info = []
        current_start = 1
        for city in path:
            dur = durations[city]
            current_end = current_start + dur - 1
            days_info.append((current_start, current_end))
            current_start = current_end
        try:
            ist_idx = path.index('Istanbul')
            santo_idx = path.index('Santorini')
        except ValueError:
            continue
        ist_start = days_info[ist_idx][0]
        santo_start = days_info[santo_idx][0]
        if ist_start == 6 and santo_start == 13:
            itinerary = []
            for i in range(len(path)):
                city = path[i]
                start, end = days_info[i]
                itinerary.append({"day_range": f"Day {start}-{end}", "place": city})
            print(json.dumps({"itinerary": itinerary}))
            return

if __name__ == "__main__":
    main()