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

    # Total vacation days is sum of all city days
    total_vacation_days = sum(days_dict.values())
    
    # Cities that must be in specific parts
    frankfurt = 'Frankfurt'
    mykonos = 'Mykonos'
    seville = 'Seville'
    fixed_part1 = [frankfurt, mykonos]  # must be in part1 (before Seville)
    
    # All cities except Seville (since Seville is fixed in the middle)
    all_cities = list(days_dict.keys())
    all_cities.remove(seville)
    remaining_cities = [city for city in all_cities if city not in fixed_part1]
    
    solution_found = False
    itinerary_result = []
    
    # Iterate over all subsets of remaining_cities to include in part1
    n = len(remaining_cities)
    for r in range(0, n+1):
        for A in itertools.combinations(remaining_cities, r):
            P1 = fixed_part1 + list(A)
            P2 = [city for city in remaining_cities if city not in A]
            
            total_p1 = sum(days_dict[city] for city in P1)
            total_p2 = sum(days_dict[city] for city in P2)
            
            # Try all permutations for part1
            for perm1 in itertools.permutations(P1):
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
                
                # Check start day constraints for Frankfurt and Mykonos
                current_day = 1
                frankfurt_ok = False
                mykonos_ok = False
                for city in perm1:
                    if city == frankfurt:
                        if current_day > 5:
                            valid1 = False
                            break
                        frankfurt_ok = True
                    if city == mykonos:
                        if current_day > 11:
                            valid1 = False
                            break
                        mykonos_ok = True
                    current_day += days_dict[city]
                
                # Must have scheduled both Frankfurt and Mykonos
                if not valid1 or not frankfurt_ok or not mykonos_ok:
                    continue
                
                # Now try part2 permutations
                for perm2 in itertools.permutations(P2):
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
                    
                    # Build the full itinerary with day ranges
                    full_itinerary = []
                    current = 1
                    # Part1
                    for city in perm1:
                        end = current + days_dict[city] - 1
                        full_itinerary.append({
                            "day_range": f"Day {current}-{end}",
                            "place": city
                        })
                        current = end + 1
                    
                    # Seville
                    end_seville = current + days_dict[seville] - 1
                    full_itinerary.append({
                        "day_range": f"Day {current}-{end_seville}",
                        "place": seville
                    })
                    current = end_seville + 1
                    
                    # Part2
                    for city in perm2:
                        end = current + days_dict[city] - 1
                        full_itinerary.append({
                            "day_range": f"Day {current}-{end}",
                            "place": city
                        })
                        current = end + 1
                    
                    # Verify total days matches
                    if current - 1 == total_vacation_days:
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
        print(json.dumps({"itinerary": itinerary_result}))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()