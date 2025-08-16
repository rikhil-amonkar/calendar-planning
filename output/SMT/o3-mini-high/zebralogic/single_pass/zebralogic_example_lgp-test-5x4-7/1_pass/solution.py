from z3 import Int, Solver, And, Distinct, Or
import json

def main():
    # Create integer variables for each attribute.
    # Names
    A_alice   = Int("Alice")
    A_peter   = Int("Peter")
    A_bob     = Int("Bob")
    A_eric    = Int("Eric")
    A_arnold  = Int("Arnold")
    # Smoothies
    S_lime         = Int("Lime")
    S_dragonfruit  = Int("Dragonfruit")
    S_desert       = Int("Desert")
    S_watermelon   = Int("Watermelon")
    S_cherry       = Int("Cherry")
    # Animals
    AN_horse  = Int("Horse")
    AN_dog    = Int("Dog")
    AN_bird   = Int("Bird")
    AN_fish   = Int("Fish")
    AN_cat    = Int("Cat")
    # Nationalities
    N_german     = Int("German")
    N_swede      = Int("Swede")
    N_norwegian  = Int("Norwegian")
    N_brit       = Int("Brit")
    N_dane       = Int("Dane")
    
    solver = Solver()
    
    # All variables can take values 1..5
    all_vars = [A_alice, A_peter, A_bob, A_eric, A_arnold,
                S_lime, S_dragonfruit, S_desert, S_watermelon, S_cherry,
                AN_horse, AN_dog, AN_bird, AN_fish, AN_cat,
                N_german, N_swede, N_norwegian, N_brit, N_dane]
    for v in all_vars:
        solver.add(And(v >= 1, v <= 5))
    
    # Each category has distinct positions.
    solver.add(Distinct(A_alice, A_peter, A_bob, A_eric, A_arnold))
    solver.add(Distinct(S_lime, S_dragonfruit, S_desert, S_watermelon, S_cherry))
    solver.add(Distinct(AN_horse, AN_dog, AN_bird, AN_fish, AN_cat))
    solver.add(Distinct(N_german, N_swede, N_norwegian, N_brit, N_dane))
    
    # Clue 1: The Swedish person is directly left of the dog owner.
    solver.add(N_swede + 1 == AN_dog)
    
    # Clue 2: There are two houses between the dog owner and the British person.
    solver.add(Or(AN_dog == N_brit + 3, N_brit == AN_dog + 3))
    
    # Clue 3: The Dane is the person who keeps horses.
    solver.add(N_dane == AN_horse)
    
    # Clue 11: The person who keeps horses is in the third house.
    solver.add(AN_horse == 3)
    
    # Clue 4: The bird keeper is somewhere to the right of the cat lover.
    solver.add(AN_bird > AN_cat)
    
    # Clue 5: The dog owner is directly left of the person who drinks Lime smoothies.
    solver.add(AN_dog + 1 == S_lime)
    
    # Clue 6: Eric is the cat lover.
    solver.add(A_eric == AN_cat)
    
    # Clue 7: Bob is the bird keeper.
    solver.add(A_bob == AN_bird)
    
    # Clue 8: The person who likes Cherry smoothies is directly left of Peter.
    solver.add(S_cherry + 1 == A_peter)
    
    # Clue 9: The bird keeper is the Watermelon smoothie lover.
    solver.add(AN_bird == S_watermelon)
    
    # Clue 10: The Desert smoothie lover is the dog owner.
    solver.add(S_desert == AN_dog)
    
    # Clue 12: The Norwegian is Alice.
    solver.add(A_alice == N_norwegian)
    
    # Solve the puzzle.
    if solver.check() == sat:
        m = solver.model()
        # Build a mapping from house number to each attribute.
        houses = {i: {} for i in range(1, 6)}
        
        # Names mapping.
        names = {
            "Alice": m[A_alice].as_long(),
            "Peter": m[A_peter].as_long(),
            "Bob": m[A_bob].as_long(),
            "Eric": m[A_eric].as_long(),
            "Arnold": m[A_arnold].as_long()
        }
        for name, pos in names.items():
            houses[pos]["Name"] = name
            
        # Smoothies mapping.
        smoothies = {
            "lime": m[S_lime].as_long(),
            "dragonfruit": m[S_dragonfruit].as_long(),
            "desert": m[S_desert].as_long(),
            "watermelon": m[S_watermelon].as_long(),
            "cherry": m[S_cherry].as_long()
        }
        for sm, pos in smoothies.items():
            houses[pos]["Smoothie"] = sm
            
        # Animals mapping.
        animals = {
            "horse": m[AN_horse].as_long(),
            "dog": m[AN_dog].as_long(),
            "bird": m[AN_bird].as_long(),
            "fish": m[AN_fish].as_long(),
            "cat": m[AN_cat].as_long()
        }
        for an, pos in animals.items():
            houses[pos]["Animal"] = an
            
        # Nationalities mapping.
        nationalities = {
            "german": m[N_german].as_long(),
            "swede": m[N_swede].as_long(),
            "norwegian": m[N_norwegian].as_long(),
            "brit": m[N_brit].as_long(),
            "dane": m[N_dane].as_long()
        }
        for nat, pos in nationalities.items():
            houses[pos]["Nationality"] = nat
        
        # Ensure every house has an entry for each attribute.
        header = ["House", "Name", "Smoothie", "Animal", "Nationality"]
        rows = []
        for i in range(1, 6):
            row = [
                str(i),
                houses[i].get("Name", ""),
                houses[i].get("Smoothie", ""),
                houses[i].get("Animal", ""),
                houses[i].get("Nationality", "")
            ]
            rows.append(row)
        
        solution = {"solution": {"header": header, "rows": rows}}
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()