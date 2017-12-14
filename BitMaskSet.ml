(* ********************************************************************************************** *
 * MetaStack Solutions Ltd.                                                                       *
 * ********************************************************************************************** *
 * BitMask Sets                                                                                   *
 * ********************************************************************************************** *
 * Copyright (c) 2013-17 MetaStack Solutions Ltd.                                                 *
 * ********************************************************************************************** *
 * Author: David Allsopp                                                                          *
 * 27-Dec-2013                                                                                    *
 * ********************************************************************************************** *
 * Redistribution and use in source and binary forms, with or without modification, are permitted *
 * provided that the following two conditions are met:                                            *
 *     1. Redistributions of source code must retain the above copyright notice, this list of     *
 *        conditions and the following disclaimer.                                                *
 *     2. Neither the name of MetaStack Solutions Ltd. nor the names of its contributors may be   *
 *        used to endorse or promote products derived from this software without specific prior   *
 *        written permission.                                                                     *
 *                                                                                                *
 * This software is provided by the Copyright Holder 'as is' and any express or implied           *
 * warranties, including, but not limited to, the implied warranties of merchantability and       *
 * fitness for a particular purpose are disclaimed. In no event shall the Copyright Holder be     *
 * liable for any direct, indirect, incidental, special, exemplary, or consequential damages      *
 * (including, but not limited to, procurement of substitute goods or services; loss of use,      *
 * data, or profits; or business interruption) however caused and on any theory of liability,     *
 * whether in contract, strict liability, or tort (including negligence or otherwise) arising in  *
 * any way out of the use of this software, even if advised of the possibility of such damage.    *
 * ********************************************************************************************** *)

(* ********************************************************************************************** *
 * Copied from header.                                                                            *
 * ********************************************************************************************** *)
module type S =
  sig
    include Set.S

    val map : (elt -> elt) -> t -> t
    val min_elt_opt : t -> elt option
    val max_elt_opt : t -> elt option
    val choose_opt : t -> elt option
    val find : elt -> t -> elt
    val find_opt : elt -> t -> elt option
    val find_first : (elt -> bool) -> t -> elt
    val find_first_opt : (elt -> bool) -> t -> elt option
    val find_last : (elt -> bool) -> t -> elt
    val find_last_opt : (elt -> bool) -> t -> elt option
    val of_list : elt list -> t

    type storage

    val invalid : t -> t
  end

module type Storage =
  sig
    type storage
    val zero : storage
    val one : storage
    val logand : storage -> storage -> storage
    val logor : storage -> storage -> storage
    val lognot : storage -> storage
    val shift_left : storage -> int -> storage
    val shift_right_logical : storage -> int -> storage
    val compare : storage -> storage -> int
    val toString : storage -> string
  end

module type BitMask =
  sig
    include Storage
    type t
    val mask : storage
    val highest : storage
    val lowest : storage
    val topbit : int
    val shifts : (int * int) list
  end

(* ********************************************************************************************** *
 * Implementations of Storage for types int and int64.                                            *
 * ********************************************************************************************** *)
module Int =
  struct
    type storage = int
    let zero = 0
    let one = 1
    let shift_left = (lsl)
    let shift_right_logical = (lsr)
    let logand = (land)
    let logor = (lor)
    let lognot = lnot
    let compare = compare
    let toString = string_of_int
  end

module Int64 =
  struct
    type storage = int64
    let zero = 0L
    let one = 1L
    let shift_left = Int64.shift_left
    let shift_right_logical = Int64.shift_right_logical
    let logand = Int64.logand
    let logor = Int64.logor
    let lognot = Int64.lognot
    let compare = Int64.compare
    let toString = Int64.to_string
  end

(* ********************************************************************************************** *
 * Make functor.                                                                                  *
 * ********************************************************************************************** *)
module Make(Mask : BitMask) =
  struct
    type storage = Mask.storage
    type t = Mask.storage

    (* ****************************************************************************************** *
     * While virtually everything else has to provided in the functor (highest, lowest, etc.),    *
     * requiring Mask.shifts to be entered twice seemed a step too far...                         *
     * ****************************************************************************************** *)
    let shiftsInv = List.rev Mask.shifts

    (* ****************************************************************************************** *
     * Prior to 1.1.0, Masks.shifts was incorrectly used by all functions except storage_of_flag  *
     * when Mask.lowest <> Mask.one. In this case, the first shift should be ignored, because     *
     * Mask.lowest has already taken it into account.                                             *
     * ****************************************************************************************** *)
    let shifts =
      match Mask.shifts with
        (0, _)::shifts -> shifts
      | _ -> Mask.shifts

    (* ****************************************************************************************** *
     * create, invalid, empty and is_empty are straightforward.                                   *
     * ****************************************************************************************** *)
    let create mask =
      mask

    let invalid mask =
      Mask.logand (Mask.lognot Mask.mask) mask

    let empty = Mask.zero

    let is_empty mask =
      (Mask.compare mask Mask.zero = 0)

    (* ****************************************************************************************** *
     * compute_shift converts a constructor index to a bit number, taking Mask.shifts into        *
     * account. It's short-circuited as the identity function for the common case of no shifts.   *
     * ****************************************************************************************** *)
    let compute_shift =
      if Mask.shifts = []
      then fun x -> x
      else fun offset ->
             let rec f a = function
               (point, amount)::shifts ->
                 if offset >= point
                 then f (a + amount) shifts
                 else a
             | [] ->
                 a
             in
               f offset Mask.shifts

    (* ****************************************************************************************** *
     * Convert a constructor to a bit.                                                            *
     * ****************************************************************************************** *)
    let storage_of_flag (flag : Mask.t) =
      let shift = compute_shift (Obj.magic flag : int)
      in
        (Mask.shift_left Mask.one shift)

    (* ****************************************************************************************** *
     * Another sequence of straightforward functions.                                             *
     * ****************************************************************************************** *)
    let mem flag set =
      Mask.compare (Mask.logand set (storage_of_flag flag)) Mask.zero <> 0

    let find flag set =
      if Mask.compare (Mask.logand set (storage_of_flag flag)) Mask.zero = 0
      then raise Not_found
      else flag

    let find_opt flag set =
      if Mask.compare (Mask.logand set (storage_of_flag flag)) Mask.zero = 0
      then None
      else Some flag

    let add flag set =
      let set' = Mask.logor set (storage_of_flag flag)
      in
        if Mask.compare set set' = 0
        then set
        else set'

    let of_list l =
      List.fold_left (fun s f -> add f s) empty l

    let singleton = storage_of_flag

    let remove flag set =
      let set' = Mask.logand set (Mask.lognot (storage_of_flag flag))
      in
        if Mask.compare set set' = 0
        then set
        else set'

    let union = Mask.logor

    let inter = Mask.logand

    let diff a b =
      Mask.logand b (Mask.lognot a)

    let compare = Mask.compare

    let equal a b =
      Mask.compare a b = 0

    let subset a b =
      Mask.compare (Mask.logand a b) a = 0

    (* ****************************************************************************************** *
     * deltaShift and deltaShiftInv are used to calculate bit values for the iterators.           *
     * ****************************************************************************************** *)
    let deltaShift i = function
      (point, amount)::shifts when i >= point ->
        (succ amount, shifts)
    | _ as shifts ->
        (1, shifts)

    let deltaShiftInv i = function
      (point, amount)::shifts when i < point ->
        (succ amount, shifts)
    | _ as shifts ->
        (1, shifts)

    (* ****************************************************************************************** *
     * @@DRA Got a feeling that horrible things would happen in these implementations if the sign *
     *       bit were included in Mask.mask...                                                    *
     *       ... so don't do that!                                                                *
     * ****************************************************************************************** *)

    (* ****************************************************************************************** *
     * The iterators count over the bit positions -- for the iterator itself, [i] is the          *
     * constructor number, [v] is the bit value for that constructor and [s] is the shifts.       *
     * ****************************************************************************************** *)

    let find_first g set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          let elt = (Obj.magic i : Mask.t)
          in
            if Mask.compare (Mask.logand set v) Mask.zero <> 0 && g elt
            then elt
            else if Mask.compare v Mask.highest = 0
                 then raise Not_found
                 else let i = succ i
                      in
                        let (shift, s) = deltaShift i s
                        in
                          f i (Mask.shift_left v shift) s
        in
          f 0 Mask.lowest shifts

    let find_first_opt g set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          let elt = (Obj.magic i : Mask.t)
          in
            if Mask.compare (Mask.logand set v) Mask.zero <> 0 && g elt
            then Some elt
            else if Mask.compare v Mask.highest = 0
                 then None
                 else let i = succ i
                      in
                        let (shift, s) = deltaShift i s
                        in
                          f i (Mask.shift_left v shift) s
        in
          f 0 Mask.lowest shifts

    let find_last g set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.zero <> 0
          then let elt = (Obj.magic i : Mask.t)
               in
                 if Mask.compare (Mask.logand v set) Mask.zero <> 0 && g elt
                 then elt
                 else let i = pred i
                      in
                        let (shift, s) = deltaShiftInv i s
                        in
                          f i (Mask.shift_right_logical v shift) s
          else raise Not_found
        in
          f Mask.topbit Mask.highest shiftsInv

    let find_last_opt g set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.zero <> 0
          then let elt = (Obj.magic i : Mask.t)
               in
                 if Mask.compare (Mask.logand v set) Mask.zero <> 0 && g elt
                 then Some elt
                 else let i = pred i
                      in
                        let (shift, s) = deltaShiftInv i s
                        in
                          f i (Mask.shift_right_logical v shift) s
          else None
        in
          f Mask.topbit Mask.highest shiftsInv

    let iter g set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.mask <= 0
          then let _ =
                 if Mask.compare (Mask.logand set v) Mask.zero <> 0
                 then g (Obj.magic i : Mask.t)
               and i = succ i
               in
                 let (shift, s) = deltaShift i s
                 in
                   f i (Mask.shift_left v shift) s
        in
          f 0 Mask.lowest shifts

    let fold g set acc =
      let set = Mask.logand set Mask.mask
      in
        let rec f a i v s =
          if Mask.compare v Mask.mask <= 0
          then let a =
                 if Mask.compare (Mask.logand set v) Mask.zero <> 0
                 then g (Obj.magic i : Mask.t) a
                 else a
               and i = succ i
               in
                 let (shift, s) = deltaShift i s
                 in
                   f a i (Mask.shift_left v shift) s
          else a
        in
          f acc 0 Mask.lowest shifts

    let map g set' =
      let set = Mask.logand set' Mask.mask
      in
        let rec f a i v s =
          if Mask.compare v Mask.highest <> 0
          then let a =
                 if Mask.compare (Mask.logand set v) Mask.zero <> 0
                 then Mask.logor a (storage_of_flag (g (Obj.magic i : Mask.t)))
                 else a
               and i = succ i
               in
                 let (shift, s) = deltaShift i s
                 in
                   f a i (Mask.shift_left v shift) s
          else if Mask.compare a set' = 0
               then set'
               else a
        in
          f Mask.zero 0 Mask.lowest shifts

    let for_all p set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.mask <= 0
          then let i' = succ i
               in
                 let (v', s) =
                   let (shift, s) = deltaShift i' s
                   in
                     (Mask.shift_left v shift, s)
                 in
                   if Mask.compare (Mask.logand set v) Mask.zero <> 0
                   then if p (Obj.magic i : Mask.t)
                        then f i' v' s
                        else false
                   else f i' v' s
          else true
        in
          f 0 Mask.lowest shifts

    let exists p set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.mask <= 0
          then let i' = succ i
               in
                 let (v', s) =
                   let (shift, s) = deltaShift i' s
                   in
                     (Mask.shift_left v shift, s)
                 in
                   if Mask.compare (Mask.logand v set) Mask.zero <> 0
                   then if p (Obj.magic i : Mask.t)
                        then true
                        else f i' v' s
                   else f i' v' s
          else false
        in
          f 0 Mask.lowest shifts

    let filter p set =
      let set = Mask.logand set Mask.mask
      in
        let rec f a i v s =
          if Mask.compare v Mask.mask <= 0
          then let a =
                 if Mask.compare (Mask.logand v set) Mask.zero <> 0 && p (Obj.magic i : Mask.t)
                 then Mask.logor a v
                 else a
               and i = succ i
               in
                 let (shift, s) = deltaShift i s
                 in
                   f a i (Mask.shift_left v shift) s
          else a
        in
          f Mask.zero 0 Mask.lowest shifts

    let partition p set =
      let set = Mask.logand set Mask.mask
      in
        let rec f ((l, r) as a) i v s =
          if Mask.compare v Mask.mask <= 0
          then let a =
                 if Mask.compare (Mask.logand v set) Mask.zero <> 0
                 then if p (Obj.magic i : Mask.t)
                      then (Mask.logor l v, r)
                      else (l, Mask.logor r v)
                 else a
               and i = succ i
               in
                 let (shift, s) = deltaShift i s
                 in
                   f a i (Mask.shift_left v shift) s
          else a
        in
          f (Mask.zero, Mask.zero) 0 Mask.lowest shifts

    let cardinal set =
      let set = Mask.logand set Mask.mask
      in
        let rec f a i v =
          if Mask.compare v Mask.mask <= 0
          then let a =
                 if Mask.compare (Mask.logand v set) Mask.zero <> 0
                 then succ a
                 else a
               in
                 f a (succ i) (Mask.shift_left v 1)
          else a
        in
          f 0 0 Mask.lowest

    let elements set =
      let set = Mask.logand set Mask.mask
      in
        let rec f a i v s =
          if Mask.compare v Mask.zero > 0
          then let a =
                 if Mask.compare (Mask.logand v set) Mask.zero <> 0
                 then (Obj.magic i : Mask.t)::a
                 else a
               and i = pred i
               in
                 let (shift, s) = deltaShiftInv i s
                 in
                   f a i (Mask.shift_right_logical v shift) s
          else a
        in
          f [] Mask.topbit Mask.highest shiftsInv

    let min_elt set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.mask <= 0
          then if Mask.compare (Mask.logand v set) Mask.zero <> 0
               then (Obj.magic i : Mask.t)
               else let i = succ i
                    in
                      let (shift, s) = deltaShift i s
                      in
                        f i (Mask.shift_left v shift) s
          else raise Not_found
        in
          f 0 Mask.lowest shifts

    let min_elt_opt set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare (Mask.logand v set) Mask.zero <> 0
          then Some (Obj.magic i : Mask.t)
          else if Mask.compare v Mask.highest = 0
               then let i = succ i
                    in
                      let (shift, s) = deltaShift i s
                      in
                        f i (Mask.shift_left v shift) s
               else None
        in
          f 0 Mask.lowest shifts

    let max_elt set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.zero > 0
          then if Mask.compare (Mask.logand v set) Mask.zero <> 0
               then (Obj.magic i : Mask.t)
               else let i = pred i
                    in
                      let (shift, s) = deltaShiftInv i s
                      in
                        f i (Mask.shift_right_logical v shift) s
          else raise Not_found
        in
          f Mask.topbit Mask.highest shiftsInv

    let max_elt_opt set =
      let set = Mask.logand set Mask.mask
      in
        let rec f i v s =
          if Mask.compare v Mask.zero <> 0
          then if Mask.compare (Mask.logand v set) Mask.zero <> 0
               then Some (Obj.magic i : Mask.t)
               else let i = pred i
                    in
                      let (shift, s) = deltaShiftInv i s
                      in
                        f i (Mask.shift_right_logical v shift) s
          else None
        in
          f Mask.topbit Mask.highest shiftsInv

    let choose = min_elt

    let choose_opt = min_elt_opt

    let split flag set =
      let flag = storage_of_flag flag
      and set = Mask.logand set Mask.mask
      in
        let rec f ((l, p, r) as a) i v s =
          if Mask.compare v Mask.mask <= 0
          then let a =
                 if Mask.compare (Mask.logand v set) Mask.zero <> 0
                 then let c = Mask.compare v flag
                      in
                        if c = 0
                        then (l, true, r)
                        else if c < 0
                             then (Mask.logor v l, p, r)
                             else (l, p, Mask.logor v r)
                 else a
               and i = succ i
               in
                 let (shift, s) = deltaShift i s
                 in
                   f a i (Mask.shift_left v shift) s
          else a
        in
          f (Mask.zero, false, Mask.zero) 0 Mask.lowest shifts
  end
