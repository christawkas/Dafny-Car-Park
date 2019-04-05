class CarPark {

    // Set for lots that have been reserved
    var reservedSpace: set<int>;

    // Set for ltos that dont have a reservation on them
    var generalSpace: set<int>;

    // Maximum number of cars in overall 
    var maxSpots: int;

    // Set of cars that have a active reservation
    var carsWRes: set<int>;


    // a constructor for the class, setting the car-park up for a new day.
    constructor (x: int)
    {
        maxSpots := x;

    }

    // to allow any car without a reservation to enter the car park.
    method enterCarPark (x: int) returns (res: bool)
    requires true;
    ensures x in generalSpace || x in reservedSpace
    ensures |generalSpace| + |reservedSpace| == old(|generalSpace|) + old(|reservedSpace|) +1
    //ensures !(x in old(reservedSpace))
    //ensures !(x in old(generalSpace)) 
    modifies this;
    {
        if (x in carsWRes && !(x in reservedSpace)) {
            reservedSpace := reservedSpace + {x};
            res := true;

        } else {
                generalSpace := generalSpace + {x};
                res := true;
        }
    }

    // to allow any car from any area to leave the car park.
    // x is the id of the car
    method leaveCarPark(x: int) returns (res: bool)
    requires true;
    // has to ensure car is not in the sets anymore
    // ensures old(generalSpace)+1 == generalSpace or old(reservedSpace)+1 == reservedSpace;
    modifies this;
    {
        
    }

    // to report on the number of non-reserved free spaces currently available.
    method checkAvailability () returns (res: int)
    requires true;
    ensures true;
    {
        res := maxSpots - |generalSpace| - |reservedSpace|;
    }
    
    // to allow a car with a reservation to enter the car park’s reserved area during its hours of operation, or to enter the car park generally outside these hours.
    method enterReservedCarPark (x: int) returns (res: int)
    {

    }
    
    // to allow a car to be registered as having a reserved space when the owner pays the subscription.
    method makeSubscription (x: int) returns (res: int)
    {

    }

    // to remove parking restrictions on the reserved spaces (i.e. at 3pm).
    method openReservedArea() returns ()
    {

    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark() returns ()
    requires true;
    ensures |generalSpace| == 0 && |reservedSpace| == 0;
    modifies this;
    {
        generalSpace := {};
        reservedSpace := {};
    }
}
method Main ()  
{
    var cp := new CarPark(5);
    
}
