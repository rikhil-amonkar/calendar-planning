import itertools
import json

def main():
    days_dict = {
        'Rome': 3,
        'Mykonos': 2,
        'Lisbon': 2,
        'Frankfurt': 5,
        'Nice': 3,
        'Stuttgart': 4,
        'Venice': 4,
        'Dublin': 2,
        'Bucharest': 2,
        'Seville': 5
    }
    
    flights = [
        "Rome and Stuttgart", 
        "Venice and Rome", 
        "Dublin and Bucharest", 
        "Mykonos and Rome", 
        "Seville and Lisbon", 
        "Frankfurt and Venice", 
        "Venice and Stuttgart", 
        "Bucharest and Lisbon", 
        "Nice and Mykonos", 
        "Venice and Lisbon", 
        "Dublin and Lisbon", 
        "Venice and Nice", 
        "Rome and Seville", 
        "Frankfurt and Rome", 
        "Nice and Dublin", 
        "Rome and Bucharest", 
        "Frankfurt and Dublin", 
        "Rome and Dublin", 
        "Venice and Dublin", 
        "Rome and Lisbon", 
        "Frankfurt and Lisbon", 
        "Nice and Rome", 
        "Frankfurt and Nice", 
        "Frankfurt and Stuttgart", 
        "Frankfurt and Bucharest", 
        "Lisbon and Stuttgart", 
        "Nice and Lisbon", 
        "Seville and Dublin"
    ]
    
    # Build graph as undirected edges
    graph = set()
    for flight in flights:
        city1, city2 = flight.split(' and ')
        edge = tuple(sorted([city1, city2]))
        graph.add(edge)
    
    def are_connected(c1, c2):
        return tuple(sorted([c1, c2])) in graph
        
    # Cities that must be in specific parts
    frankfurt = 'Frankfurt'
    mykonos = 'Mykonos'
    seville = 'Seville'
    fixed_part1 = [frankfurt, mykonos]  # must be in part1 (before Seville)
    remaining_cities = ['Rome', 'Lisbon', 'Nice', 'Stuttgart', 'Venice', 'Dublin', 'Bucharest']
    
    # Precompute all subsets of remaining cities for part1 (5 days) and part2 (6 days)
    subsets_part1 = []
    for r in range(1, len(remaining_cities)+1):
        for subset in itertools.combinations(remaining_cities, r):
            total = sum(days_dict[city] for city in subset)
            if total == 5:
                subsets_part1.append(set(subset))
    
    solution_found = False
    itinerary_result = []
    
    for A in subsets_part1:
        # Get the remaining cities not in A
        remaining_minus_A = [city for city in remaining_cities if city not in A]
        # Now find subset B from remaining_minus_A that sums to 6 days
        for s in range(1, len(remaining_minus_A)+1):
            for B in itertools.combinations(remaining_minus_A, s):
                if sum(days_dict[city] for city in B) != 6:
                    continue
                B = set(B)
                # We have A (5 days) and B (6 days), and they are disjoint
                set1 = fixed_part1 + list(A)   # cities for part1
                set2 = list(B)                 # cities for part2
                
                # Try all permutations for part1
                for perm1 in itertools.permutations(set1):
                    # Check connectivity in part1
                    valid1 = True
                    for i in range(len(perm1)-1):
                        if not are_connected(perm1[i], perm1[i+1]):
                            valid1 = False
                            break
                    if not valid1:
                        continue
                    
                    # Last city of part1 must connect to Seville
                    if not are_connected(perm1[-1], seville):
                        continue
                    
                    # Build timeline for part1 and check Frankfurt/Mykonos start days
                    start = 1
                    frankfurt_start = None
                    mykonos_start = None
                    for city in perm1:
                        if city == frankfurt:
                            frankfurt_start = start
                        if city == mykonos:
                            mykonos_start = start
                        start += days_dict[city]
                    
                    # Part1 must end at day12 (so Seville starts at 13)
                    if start != 13:
                        continue
                    
                    # Check constraints for Frankfurt and Mykonos
                    if frankfurt_start is not None and frankfurt_start > 5:
                        continue
                    if mykonos_start is not None and mykonos_start > 11:
                        continue
                    
                    # Now try part2 permutations
                    for perm2 in itertools.permutations(set2):
                        # Check connectivity in part2
                        valid2 = True
                        for i in range(len(perm2)-1):
                            if not are_connected(perm2[i], perm2[i+1]):
                                valid2 = False
                                break
                        if not valid2:
                            continue
                        
                        # First city of part2 must connect to Seville
                        if not are_connected(seville, perm2[0]):
                            continue
                        
                        # We have a valid full itinerary: [part1] -> Seville -> [part2]
                        # Build the full itinerary with day ranges
                        full_itinerary = []
                        current_day = 1
                        # Part1
                        for city in perm1:
                            end_day = current_day + days_dict[city] - 1
                            full_itinerary.append({
                                "day_range": f"Day {current_day}-{end_day}",
                                "place": city
                            })
                            current_day = end_day + 1
                        # Seville
                        end_seville = current_day + days_dict[seville] - 1
                        full_itinerary.append({
                            "day_range": f"Day {current_day}-{end_seville}",
                            "place": seville
                        })
                        current_day = end_seville + 1
                        # Part2
                        for city in perm2:
                            end_day = current_day + days_dict[city] - 1
                            full_itinerary.append({
                                "day_range": f"Day {current_day}-{end_day}",
                                "place": city
                            })
                            current_day = end_day + 1
                        
                        # Should end on day23
                        if current_day - 1 == 23:
                            itinerary_result = full_itinerary
                            solution_found = True
                            break
                    
                    if solution_found:
                        break
                if solution_found:
                    break
            if solution_found:
                break
        if solution_found:
            break
            
    if solution_found:
        print(json.dumps({"itinerary": itinerary_result}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()