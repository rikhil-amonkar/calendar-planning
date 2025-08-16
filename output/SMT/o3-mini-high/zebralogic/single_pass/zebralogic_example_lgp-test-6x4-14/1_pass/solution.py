from z3 import *
import json

def main():
    s = Solver()
    
    # Create integer variables representing the house number (1 to 6)
    # Names:
    Eric   = Int('Eric')
    Bob    = Int('Bob')
    Peter  = Int('Peter')
    Alice  = Int('Alice')
    Arnold = Int('Arnold')
    Carol  = Int('Carol')
    
    # Car models:
    ford_f150             = Int('ford_f150')
    honda_civic           = Int('honda_civic')
    toyota_camry          = Int('toyota_camry')
    tesla_model_3         = Int('tesla_model_3')
    chevrolet_silverado   = Int('chevrolet_silverado')
    bmw_3_series          = Int('bmw_3_series')
    
    # Mothers:
    Sarah   = Int('Sarah')
    Penny   = Int('Penny')
    Holly   = Int('Holly')
    Aniya   = Int('Aniya')
    Kailyn  = Int('Kailyn')
    Janelle = Int('Janelle')
    
    # Hobbies:
    photography = Int('photography')
    cooking     = Int('cooking')
    knitting    = Int('knitting')
    gardening   = Int('gardening')
    woodworking = Int('woodworking')
    painting    = Int('painting')
    
    # List of all variables
    vars_all = [Eric, Bob, Peter, Alice, Arnold, Carol,
                ford_f150, honda_civic, toyota_camry, tesla_model_3, chevrolet_silverado, bmw_3_series,
                Sarah, Penny, Holly, Aniya, Kailyn, Janelle,
                photography, cooking, knitting, gardening, woodworking, painting]
    
    # Each variable must be in the range 1..6 (representing house positions)
    for var in vars_all:
        s.add(var >= 1, var <= 6)
    
    # Each category's elements are all in different houses.
    s.add(Distinct(Eric, Bob, Peter, Alice, Arnold, Carol))
    s.add(Distinct(ford_f150, honda_civic, toyota_camry, tesla_model_3, chevrolet_silverado, bmw_3_series))
    s.add(Distinct(Sarah, Penny, Holly, Aniya, Kailyn, Janelle))
    s.add(Distinct(photography, cooking, knitting, gardening, woodworking, painting))
    
    # ----- Encode the clues -----
    # 1. The person who owns a Toyota Camry is in the sixth house.
    s.add(toyota_camry == 6)
    
    # 2. Carol is the photography enthusiast.
    s.add(Carol == photography)
    
    # 3. The person who owns a Chevrolet Silverado is the person whose mother's name is Aniya.
    s.add(chevrolet_silverado == Aniya)
    
    # 4. The person who owns a Chevrolet Silverado is not in the second house.
    s.add(chevrolet_silverado != 2)
    
    # 5. The person who owns a Ford F-150 is the person whose mother's name is Sarah.
    s.add(ford_f150 == Sarah)
    
    # 6. The person who owns a BMW 3 Series is Bob.
    s.add(bmw_3_series == Bob)
    
    # 7. The person whose mother's name is Kailyn is in the sixth house.
    s.add(Kailyn == 6)
    
    # 8. Eric is directly left of the person who enjoys knitting.
    s.add(Eric + 1 == knitting)
    
    # 9. There is one house between the person whose mother's name is Sarah and the person who owns a Toyota Camry.
    s.add(Abs(Sarah - toyota_camry) == 2)  # Given toyota_camry==6, this forces Sarah == 4.
    
    # 10. The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    s.add(Penny > knitting)
    
    # 11. The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    s.add(Aniya > honda_civic)
    
    # 12. Alice is somewhere to the right of the person who owns a Ford F-150.
    s.add(Alice > ford_f150)
    
    # 13. Eric is the person who enjoys gardening.
    s.add(Eric == gardening)
    
    # 14. The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    s.add(woodworking < knitting)
    
    # 15. There is one house between the person whose mother's name is Sarah and the person who loves cooking.
    s.add(Abs(Sarah - cooking) == 2)
    
    # 16. The person who owns a Honda Civic is Arnold.
    s.add(honda_civic == Arnold)
    
    # 17. The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    s.add(Holly + 1 == knitting)
    
    # Additional deduction: Since both Eric and Holly are directly left of the knitting house,
    # they must be in the same house.
    s.add(Eric == Holly)
    
    # Since clue 9 forces Sarah to be 2 houses apart from house 6, we also get:
    s.add(Sarah == 4)
    # And clue 5 gives ford_f150 == Sarah, so:
    s.add(ford_f150 == 4)
    
    # Clue 6 already sets bmw_3_series equal to Bob,
    # and clue 16 sets honda_civic equal to Arnold.
    # Clue 3 sets chevrolet_silverado equal to Aniya.
    
    # Solve the puzzle.
    if s.check() == sat:
        m = s.model()
        # Build reverse mappings: for each house, find the name, car, mother and hobby assigned there.
        names_dict = {
            m.evaluate(Eric).as_long(): "Eric",
            m.evaluate(Bob).as_long(): "Bob",
            m.evaluate(Peter).as_long(): "Peter",
            m.evaluate(Alice).as_long(): "Alice",
            m.evaluate(Arnold).as_long(): "Arnold",
            m.evaluate(Carol).as_long(): "Carol"
        }
        cars_dict = {
            m.evaluate(ford_f150).as_long(): "ford f150",
            m.evaluate(honda_civic).as_long(): "honda civic",
            m.evaluate(toyota_camry).as_long(): "toyota camry",
            m.evaluate(tesla_model_3).as_long(): "tesla model 3",
            m.evaluate(chevrolet_silverado).as_long(): "chevrolet silverado",
            m.evaluate(bmw_3_series).as_long(): "bmw 3 series"
        }
        mothers_dict = {
            m.evaluate(Sarah).as_long(): "Sarah",
            m.evaluate(Penny).as_long(): "Penny",
            m.evaluate(Holly).as_long(): "Holly",
            m.evaluate(Aniya).as_long(): "Aniya",
            m.evaluate(Kailyn).as_long(): "Kailyn",
            m.evaluate(Janelle).as_long(): "Janelle"
        }
        hobbies_dict = {
            m.evaluate(photography).as_long(): "photography",
            m.evaluate(cooking).as_long(): "cooking",
            m.evaluate(knitting).as_long(): "knitting",
            m.evaluate(gardening).as_long(): "gardening",
            m.evaluate(woodworking).as_long(): "woodworking",
            m.evaluate(painting).as_long(): "painting"
        }
        
        # Build rows for houses 1 to 6 in order.
        rows = []
        for house in range(1, 7):
            row = [
                str(house),
                names_dict.get(house, ""),
                cars_dict.get(house, ""),
                mothers_dict.get(house, ""),
                hobbies_dict.get(house, "")
            ]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")
        
if __name__ == "__main__":
    main()